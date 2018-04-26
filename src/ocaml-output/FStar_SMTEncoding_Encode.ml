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
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3440 =
      let uu____3441 =
        let uu____3448 =
          let uu____3449 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3449 range_ty  in
        let uu____3450 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3448, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3450)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3441  in
    [uu____3440]  in
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
        let uu____3490 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3490 x1 t  in
      let uu____3491 =
        let uu____3502 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3502)  in
      FStar_SMTEncoding_Util.mkForall uu____3491  in
    let uu____3525 =
      let uu____3526 =
        let uu____3533 =
          let uu____3534 =
            let uu____3545 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3545)  in
          FStar_SMTEncoding_Util.mkForall uu____3534  in
        (uu____3533,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3526  in
    [uu____3525]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3601 =
      let uu____3602 =
        let uu____3609 =
          let uu____3610 =
            let uu____3625 =
              let uu____3626 =
                let uu____3631 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3632 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3631, uu____3632)  in
              FStar_SMTEncoding_Util.mkAnd uu____3626  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3625)
             in
          FStar_SMTEncoding_Util.mkForall' uu____3610  in
        (uu____3609,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3602  in
    [uu____3601]  in
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
          let uu____4048 =
            FStar_Util.find_opt
              (fun uu____4080  ->
                 match uu____4080 with
                 | (l,uu____4092) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4048 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4126,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4177 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4177 with
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
              let uu____4229 =
                ((let uu____4232 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4232) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4229
              then
                let arg_sorts =
                  let uu____4242 =
                    let uu____4243 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4243.FStar_Syntax_Syntax.n  in
                  match uu____4242 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4249) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4279  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4284 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4286 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4286 with
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
                (let uu____4319 = prims.is lid  in
                 if uu____4319
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4327 = prims.mk lid vname  in
                   match uu____4327 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4354 =
                      let uu____4365 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4365 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4383 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4383
                            then
                              let uu____4384 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___82_4387 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___82_4387.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___82_4387.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___82_4387.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___82_4387.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___82_4387.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___82_4387.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___82_4387.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___82_4387.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___82_4387.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___82_4387.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___82_4387.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___82_4387.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___82_4387.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___82_4387.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___82_4387.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___82_4387.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___82_4387.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___82_4387.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___82_4387.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___82_4387.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___82_4387.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___82_4387.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___82_4387.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___82_4387.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___82_4387.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___82_4387.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___82_4387.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___82_4387.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___82_4387.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___82_4387.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___82_4387.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___82_4387.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___82_4387.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___82_4387.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___82_4387.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___82_4387.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4384
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4399 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4399)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4354 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4449 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4449 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4474 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___71_4524  ->
                                       match uu___71_4524 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4528 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4528 with
                                            | (uu____4549,(xxsym,uu____4551))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4569 =
                                                  let uu____4570 =
                                                    let uu____4577 =
                                                      let uu____4578 =
                                                        let uu____4589 =
                                                          let uu____4590 =
                                                            let uu____4595 =
                                                              let uu____4596
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4596
                                                               in
                                                            (vapp,
                                                              uu____4595)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4590
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4589)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4578
                                                       in
                                                    (uu____4577,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4570
                                                   in
                                                [uu____4569])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4615 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4615 with
                                            | (uu____4636,(xxsym,uu____4638))
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
                                                let uu____4661 =
                                                  let uu____4662 =
                                                    let uu____4669 =
                                                      let uu____4670 =
                                                        let uu____4681 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4681)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4670
                                                       in
                                                    (uu____4669,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4662
                                                   in
                                                [uu____4661])
                                       | uu____4698 -> []))
                                in
                             let uu____4699 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____4699 with
                              | (vars,guards,env',decls1,uu____4726) ->
                                  let uu____4739 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4748 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____4748, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____4750 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____4750 with
                                         | (g,ds) ->
                                             let uu____4761 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____4761,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____4739 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____4774 =
                                           let uu____4781 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____4781)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____4774
                                          in
                                       let uu____4790 =
                                         let vname_decl =
                                           let uu____4798 =
                                             let uu____4809 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____4819  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____4809,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____4798
                                            in
                                         let uu____4828 =
                                           let env2 =
                                             let uu___83_4834 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___83_4834.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____4835 =
                                             let uu____4836 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____4836  in
                                           if uu____4835
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____4828 with
                                         | (tok_typing,decls2) ->
                                             let uu____4850 =
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
                                                   let uu____4870 =
                                                     let uu____4871 =
                                                       let uu____4874 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____4874
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____4871
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____4870)
                                               | uu____4883 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____4890 =
                                                       let uu____4897 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____4897]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____4890
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____4904 =
                                                       let uu____4915 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____4915)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____4904
                                                      in
                                                   let name_tok_corr =
                                                     let uu____4927 =
                                                       let uu____4934 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____4934,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____4927
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
                                                       let uu____4963 =
                                                         let uu____4974 =
                                                           let uu____4975 =
                                                             let uu____4980 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____4981 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____4980,
                                                               uu____4981)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____4975
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____4974)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____4963
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
                                             (match uu____4850 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____4790 with
                                        | (decls2,env2) ->
                                            let uu____5034 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5042 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5042 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5055 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5055,
                                                    decls)
                                               in
                                            (match uu____5034 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5066 =
                                                     let uu____5073 =
                                                       let uu____5074 =
                                                         let uu____5085 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5085)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____5074
                                                        in
                                                     (uu____5073,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5066
                                                    in
                                                 let freshness =
                                                   let uu____5101 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5101
                                                   then
                                                     let uu____5106 =
                                                       let uu____5107 =
                                                         let uu____5118 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5129 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5118,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5129)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5107
                                                        in
                                                     let uu____5132 =
                                                       let uu____5135 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____5135]  in
                                                     uu____5106 :: uu____5132
                                                   else []  in
                                                 let g =
                                                   let uu____5140 =
                                                     let uu____5143 =
                                                       let uu____5146 =
                                                         let uu____5149 =
                                                           let uu____5152 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5152
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5149
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5146
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5143
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5140
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
          let uu____5185 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5185 with
          | FStar_Pervasives_Native.None  ->
              let uu____5196 = encode_free_var false env x t t_norm []  in
              (match uu____5196 with
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
            let uu____5259 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5259 with
            | (decls,env1) ->
                let uu____5278 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5278
                then
                  let uu____5285 =
                    let uu____5288 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5288  in
                  (uu____5285, env1)
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
             (fun uu____5346  ->
                fun lb  ->
                  match uu____5346 with
                  | (decls,env1) ->
                      let uu____5366 =
                        let uu____5373 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5373
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5366 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5396 = FStar_Syntax_Util.head_and_args t  in
    match uu____5396 with
    | (hd1,args) ->
        let uu____5433 =
          let uu____5434 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5434.FStar_Syntax_Syntax.n  in
        (match uu____5433 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5438,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5457 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5463 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5491  ->
      fun quals  ->
        match uu____5491 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5575 = FStar_Util.first_N nbinders formals  in
              match uu____5575 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____5656  ->
                         fun uu____5657  ->
                           match (uu____5656, uu____5657) with
                           | ((formal,uu____5675),(binder,uu____5677)) ->
                               let uu____5686 =
                                 let uu____5693 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____5693)  in
                               FStar_Syntax_Syntax.NT uu____5686) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____5701 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____5732  ->
                              match uu____5732 with
                              | (x,i) ->
                                  let uu____5743 =
                                    let uu___84_5744 = x  in
                                    let uu____5745 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___84_5744.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___84_5744.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5745
                                    }  in
                                  (uu____5743, i)))
                       in
                    FStar_All.pipe_right uu____5701
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____5763 =
                      let uu____5768 = FStar_Syntax_Subst.compress body  in
                      let uu____5769 =
                        let uu____5770 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____5770
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____5768 uu____5769
                       in
                    uu____5763 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____5839 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____5839
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___85_5842 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___85_5842.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___85_5842.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___85_5842.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___85_5842.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___85_5842.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___85_5842.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___85_5842.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___85_5842.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___85_5842.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___85_5842.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___85_5842.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___85_5842.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___85_5842.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___85_5842.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___85_5842.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___85_5842.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___85_5842.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___85_5842.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___85_5842.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___85_5842.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___85_5842.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___85_5842.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___85_5842.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___85_5842.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___85_5842.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___85_5842.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___85_5842.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___85_5842.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___85_5842.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___85_5842.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___85_5842.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___85_5842.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___85_5842.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___85_5842.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___85_5842.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___85_5842.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____5879 = FStar_Syntax_Util.abs_formals e  in
                match uu____5879 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____5943::uu____5944 ->
                         let uu____5959 =
                           let uu____5960 =
                             let uu____5963 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____5963
                              in
                           uu____5960.FStar_Syntax_Syntax.n  in
                         (match uu____5959 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6006 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6006 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6048 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6048
                                   then
                                     let uu____6083 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6083 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6177  ->
                                                   fun uu____6178  ->
                                                     match (uu____6177,
                                                             uu____6178)
                                                     with
                                                     | ((x,uu____6196),
                                                        (b,uu____6198)) ->
                                                         let uu____6207 =
                                                           let uu____6214 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6214)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6207)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6216 =
                                            let uu____6237 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6237)  in
                                          (uu____6216, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6305 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6305 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6394) ->
                              let uu____6399 =
                                let uu____6420 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6420  in
                              (uu____6399, true)
                          | uu____6485 when Prims.op_Negation norm1 ->
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
                          | uu____6487 ->
                              let uu____6488 =
                                let uu____6489 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6490 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6489 uu____6490
                                 in
                              failwith uu____6488)
                     | uu____6515 ->
                         let rec aux' t_norm2 =
                           let uu____6542 =
                             let uu____6543 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6543.FStar_Syntax_Syntax.n  in
                           match uu____6542 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6584 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6584 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____6612 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____6612 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____6692) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____6697 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____6753 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____6753
               then encode_top_level_vals env bindings quals
               else
                 (let uu____6765 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____6828  ->
                            fun lb  ->
                              match uu____6828 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____6883 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____6883
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____6886 =
                                      let uu____6895 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____6895
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____6886 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____6765 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7020 =
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
                        | uu____7026 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7034 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7034 vars)
                            else
                              (let uu____7036 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7036)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7096;
                             FStar_Syntax_Syntax.lbeff = uu____7097;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7099;
                             FStar_Syntax_Syntax.lbpos = uu____7100;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7124 =
                              let uu____7131 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7131 with
                              | (tcenv',uu____7149,e_t) ->
                                  let uu____7155 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7166 -> failwith "Impossible"  in
                                  (match uu____7155 with
                                   | (e1,t_norm1) ->
                                       ((let uu___88_7182 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___88_7182.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___88_7182.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___88_7182.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___88_7182.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___88_7182.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____7124 with
                             | (env',e1,t_norm1) ->
                                 let uu____7192 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7192 with
                                  | ((binders,body,uu____7213,t_body),curry)
                                      ->
                                      ((let uu____7225 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7225
                                        then
                                          let uu____7226 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7227 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7226 uu____7227
                                        else ());
                                       (let uu____7229 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7229 with
                                        | (vars,guards,env'1,binder_decls,uu____7256)
                                            ->
                                            let body1 =
                                              let uu____7270 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7270
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
                                              let uu____7287 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7287 curry fvb
                                                vars
                                               in
                                            let uu____7288 =
                                              let uu____7297 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7297
                                              then
                                                let uu____7308 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7309 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7308, uu____7309)
                                              else
                                                (let uu____7319 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7319))
                                               in
                                            (match uu____7288 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7342 =
                                                     let uu____7349 =
                                                       let uu____7350 =
                                                         let uu____7361 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7361)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____7350
                                                        in
                                                     let uu____7372 =
                                                       let uu____7375 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7375
                                                        in
                                                     (uu____7349, uu____7372,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7342
                                                    in
                                                 let uu____7378 =
                                                   let uu____7381 =
                                                     let uu____7384 =
                                                       let uu____7387 =
                                                         let uu____7390 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7390
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7387
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7384
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7381
                                                    in
                                                 (uu____7378, env2))))))
                        | uu____7395 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7458 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7458, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7461 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7508  ->
                                  fun fvb  ->
                                    match uu____7508 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7554 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7554
                                           in
                                        let gtok =
                                          let uu____7556 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7556
                                           in
                                        let env4 =
                                          let uu____7558 =
                                            let uu____7561 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____7561
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7558
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7461 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____7669 t_norm
                              uu____7671 =
                              match (uu____7669, uu____7671) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____7701;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____7702;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____7704;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____7705;_})
                                  ->
                                  let uu____7726 =
                                    let uu____7733 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____7733 with
                                    | (tcenv',uu____7755,e_t) ->
                                        let uu____7761 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____7772 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____7761 with
                                         | (e1,t_norm1) ->
                                             ((let uu___89_7788 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___89_7788.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____7726 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____7803 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____7803
                                         then
                                           let uu____7804 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____7805 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____7806 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____7804 uu____7805 uu____7806
                                         else ());
                                        (let uu____7808 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____7808 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____7845 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____7845
                                               then
                                                 let uu____7846 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____7847 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____7848 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____7849 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____7846 uu____7847
                                                   uu____7848 uu____7849
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____7853 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____7853 with
                                               | (vars,guards,env'1,binder_decls,uu____7884)
                                                   ->
                                                   let decl_g =
                                                     let uu____7898 =
                                                       let uu____7909 =
                                                         let uu____7912 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____7912
                                                          in
                                                       (g, uu____7909,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____7898
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
                                                     let uu____7937 =
                                                       let uu____7944 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____7944)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7937
                                                      in
                                                   let gsapp =
                                                     let uu____7954 =
                                                       let uu____7961 =
                                                         let uu____7964 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____7964 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____7961)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7954
                                                      in
                                                   let gmax =
                                                     let uu____7970 =
                                                       let uu____7977 =
                                                         let uu____7980 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____7980 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____7977)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7970
                                                      in
                                                   let body1 =
                                                     let uu____7986 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____7986
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____7988 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____7988 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8006 =
                                                            let uu____8013 =
                                                              let uu____8014
                                                                =
                                                                let uu____8029
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
                                                                  uu____8029)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____8014
                                                               in
                                                            let uu____8050 =
                                                              let uu____8053
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8053
                                                               in
                                                            (uu____8013,
                                                              uu____8050,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8006
                                                           in
                                                        let eqn_f =
                                                          let uu____8057 =
                                                            let uu____8064 =
                                                              let uu____8065
                                                                =
                                                                let uu____8076
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8076)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____8065
                                                               in
                                                            (uu____8064,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8057
                                                           in
                                                        let eqn_g' =
                                                          let uu____8090 =
                                                            let uu____8097 =
                                                              let uu____8098
                                                                =
                                                                let uu____8109
                                                                  =
                                                                  let uu____8110
                                                                    =
                                                                    let uu____8115
                                                                    =
                                                                    let uu____8116
                                                                    =
                                                                    let uu____8123
                                                                    =
                                                                    let uu____8126
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8126
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8123)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8116
                                                                     in
                                                                    (gsapp,
                                                                    uu____8115)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8110
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8109)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____8098
                                                               in
                                                            (uu____8097,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8090
                                                           in
                                                        let uu____8149 =
                                                          let uu____8158 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8158
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8187)
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
                                                                  let uu____8212
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8212
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8217
                                                                  =
                                                                  let uu____8224
                                                                    =
                                                                    let uu____8225
                                                                    =
                                                                    let uu____8236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8236)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____8225
                                                                     in
                                                                  (uu____8224,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8217
                                                                 in
                                                              let uu____8257
                                                                =
                                                                let uu____8264
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8264
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8277
                                                                    =
                                                                    let uu____8280
                                                                    =
                                                                    let uu____8281
                                                                    =
                                                                    let uu____8288
                                                                    =
                                                                    let uu____8289
                                                                    =
                                                                    let uu____8300
                                                                    =
                                                                    let uu____8301
                                                                    =
                                                                    let uu____8306
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8306,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8301
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8300)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____8289
                                                                     in
                                                                    (uu____8288,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8281
                                                                     in
                                                                    [uu____8280]
                                                                     in
                                                                    (d3,
                                                                    uu____8277)
                                                                 in
                                                              (match uu____8257
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
                                                        (match uu____8149
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
                            let uu____8371 =
                              let uu____8384 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8445  ->
                                   fun uu____8446  ->
                                     match (uu____8445, uu____8446) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8571 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8571 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8384
                               in
                            (match uu____8371 with
                             | (decls2,eqns,env01) ->
                                 let uu____8644 =
                                   let isDeclFun uu___72_8658 =
                                     match uu___72_8658 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____8659 -> true
                                     | uu____8670 -> false  in
                                   let uu____8671 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____8671
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____8644 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____8711 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___73_8715  ->
                                 match uu___73_8715 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____8716 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____8722 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____8722)))
                         in
                      if uu____8711
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
                   let uu____8774 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____8774
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
        let uu____8835 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____8835 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____8839 = encode_sigelt' env se  in
      match uu____8839 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____8855 =
                  let uu____8856 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____8856  in
                [uu____8855]
            | uu____8857 ->
                let uu____8858 =
                  let uu____8861 =
                    let uu____8862 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____8862  in
                  uu____8861 :: g  in
                let uu____8863 =
                  let uu____8866 =
                    let uu____8867 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____8867  in
                  [uu____8866]  in
                FStar_List.append uu____8858 uu____8863
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
        let uu____8882 =
          let uu____8883 = FStar_Syntax_Subst.compress t  in
          uu____8883.FStar_Syntax_Syntax.n  in
        match uu____8882 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____8887)) -> s = "opaque_to_smt"
        | uu____8888 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____8895 =
          let uu____8896 = FStar_Syntax_Subst.compress t  in
          uu____8896.FStar_Syntax_Syntax.n  in
        match uu____8895 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____8900)) -> s = "uninterpreted_by_smt"
        | uu____8901 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8906 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____8911 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____8922 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____8925 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____8928 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8943 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8947 =
            let uu____8948 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____8948 Prims.op_Negation  in
          if uu____8947
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____8976 ->
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
               let uu____9000 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9000 with
               | (formals,uu____9018) ->
                   let arity = FStar_List.length formals  in
                   let uu____9036 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9036 with
                    | (aname,atok,env2) ->
                        let uu____9056 =
                          let uu____9061 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9061
                            env2
                           in
                        (match uu____9056 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9073 =
                                 let uu____9074 =
                                   let uu____9085 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9101  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9085,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9074
                                  in
                               [uu____9073;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9114 =
                               let aux uu____9170 uu____9171 =
                                 match (uu____9170, uu____9171) with
                                 | ((bv,uu____9223),(env3,acc_sorts,acc)) ->
                                     let uu____9261 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9261 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9114 with
                              | (uu____9333,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9356 =
                                      let uu____9363 =
                                        let uu____9364 =
                                          let uu____9375 =
                                            let uu____9376 =
                                              let uu____9381 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9381)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9376
                                             in
                                          ([[app]], xs_sorts, uu____9375)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____9364
                                         in
                                      (uu____9363,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9356
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
                                    let uu____9401 =
                                      let uu____9408 =
                                        let uu____9409 =
                                          let uu____9420 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9420)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____9409
                                         in
                                      (uu____9408,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9401
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9439 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9439 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9467,uu____9468) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9469 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9469 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9486,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9492 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___74_9496  ->
                      match uu___74_9496 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9497 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9502 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9503 -> false))
               in
            Prims.op_Negation uu____9492  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9512 =
               let uu____9519 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9519 env fv t quals  in
             match uu____9512 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9534 =
                   let uu____9537 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9537  in
                 (uu____9534, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9545 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9545 with
           | (uu____9554,f1) ->
               let uu____9556 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env  in
               (match uu____9556 with
                | (f2,decls) ->
                    let g =
                      let uu____9570 =
                        let uu____9571 =
                          let uu____9578 =
                            let uu____9581 =
                              let uu____9582 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9582
                               in
                            FStar_Pervasives_Native.Some uu____9581  in
                          let uu____9583 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____9578, uu____9583)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9571  in
                      [uu____9570]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9589) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____9601 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____9619 =
                       let uu____9622 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____9622.FStar_Syntax_Syntax.fv_name  in
                     uu____9619.FStar_Syntax_Syntax.v  in
                   let uu____9623 =
                     let uu____9624 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____9624  in
                   if uu____9623
                   then
                     let val_decl =
                       let uu___92_9652 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___92_9652.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___92_9652.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___92_9652.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____9657 = encode_sigelt' env1 val_decl  in
                     match uu____9657 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____9601 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____9685,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                         FStar_Syntax_Syntax.lbunivs = uu____9687;
                         FStar_Syntax_Syntax.lbtyp = uu____9688;
                         FStar_Syntax_Syntax.lbeff = uu____9689;
                         FStar_Syntax_Syntax.lbdef = uu____9690;
                         FStar_Syntax_Syntax.lbattrs = uu____9691;
                         FStar_Syntax_Syntax.lbpos = uu____9692;_}::[]),uu____9693)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____9716 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____9716 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____9745 =
                   let uu____9748 =
                     let uu____9749 =
                       let uu____9756 =
                         let uu____9757 =
                           let uu____9768 =
                             let uu____9769 =
                               let uu____9774 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____9774)  in
                             FStar_SMTEncoding_Util.mkEq uu____9769  in
                           ([[b2t_x]], [xx], uu____9768)  in
                         FStar_SMTEncoding_Util.mkForall uu____9757  in
                       (uu____9756, (FStar_Pervasives_Native.Some "b2t def"),
                         "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____9749  in
                   [uu____9748]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____9745
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____9807,uu____9808) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___75_9817  ->
                  match uu___75_9817 with
                  | FStar_Syntax_Syntax.Discriminator uu____9818 -> true
                  | uu____9819 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____9822,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____9833 =
                     let uu____9834 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____9834.FStar_Ident.idText  in
                   uu____9833 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___76_9838  ->
                     match uu___76_9838 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____9839 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____9843) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___77_9860  ->
                  match uu___77_9860 with
                  | FStar_Syntax_Syntax.Projector uu____9861 -> true
                  | uu____9866 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____9869 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____9869 with
           | FStar_Pervasives_Native.Some uu____9876 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___93_9880 = se  in
                 let uu____9881 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____9881;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___93_9880.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___93_9880.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___93_9880.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____9888) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9906) ->
          let uu____9915 = encode_sigelts env ses  in
          (match uu____9915 with
           | (g,env1) ->
               let uu____9932 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___78_9955  ->
                         match uu___78_9955 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____9956;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____9957;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____9958;_}
                             -> false
                         | uu____9961 -> true))
                  in
               (match uu____9932 with
                | (g',inversions) ->
                    let uu____9976 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___79_9997  ->
                              match uu___79_9997 with
                              | FStar_SMTEncoding_Term.DeclFun uu____9998 ->
                                  true
                              | uu____10009 -> false))
                       in
                    (match uu____9976 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10027,tps,k,uu____10030,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___80_10047  ->
                    match uu___80_10047 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10048 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10059 = c  in
              match uu____10059 with
              | (name,args,uu____10064,uu____10065,uu____10066) ->
                  let uu____10071 =
                    let uu____10072 =
                      let uu____10083 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10100  ->
                                match uu____10100 with
                                | (uu____10107,sort,uu____10109) -> sort))
                         in
                      (name, uu____10083, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10072  in
                  [uu____10071]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____10140 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10146 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10146 FStar_Option.isNone))
               in
            if uu____10140
            then []
            else
              (let uu____10178 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10178 with
               | (xxsym,xx) ->
                   let uu____10187 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10226  ->
                             fun l  ->
                               match uu____10226 with
                               | (out,decls) ->
                                   let uu____10246 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10246 with
                                    | (uu____10257,data_t) ->
                                        let uu____10259 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10259 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10305 =
                                                 let uu____10306 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10306.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10305 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10317,indices) ->
                                                   indices
                                               | uu____10339 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10363  ->
                                                         match uu____10363
                                                         with
                                                         | (x,uu____10369) ->
                                                             let uu____10370
                                                               =
                                                               let uu____10371
                                                                 =
                                                                 let uu____10378
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10378,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10371
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10370)
                                                    env)
                                                in
                                             let uu____10381 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10381 with
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
                                                      let uu____10407 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10423
                                                                 =
                                                                 let uu____10428
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10428,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10423)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10407
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10431 =
                                                      let uu____10432 =
                                                        let uu____10437 =
                                                          let uu____10438 =
                                                            let uu____10443 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10443,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10438
                                                           in
                                                        (out, uu____10437)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10432
                                                       in
                                                    (uu____10431,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10187 with
                    | (data_ax,decls) ->
                        let uu____10456 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10456 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10467 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10467 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10471 =
                                 let uu____10478 =
                                   let uu____10479 =
                                     let uu____10490 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10505 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10490,
                                       uu____10505)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____10479
                                    in
                                 let uu____10520 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10478,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10520)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10471
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10523 =
            let uu____10536 =
              let uu____10537 = FStar_Syntax_Subst.compress k  in
              uu____10537.FStar_Syntax_Syntax.n  in
            match uu____10536 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10582 -> (tps, k)  in
          (match uu____10523 with
           | (formals,res) ->
               let uu____10605 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____10605 with
                | (formals1,res1) ->
                    let uu____10616 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____10616 with
                     | (vars,guards,env',binder_decls,uu____10641) ->
                         let arity = FStar_List.length vars  in
                         let uu____10655 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____10655 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____10678 =
                                  let uu____10685 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____10685)  in
                                FStar_SMTEncoding_Util.mkApp uu____10678  in
                              let uu____10694 =
                                let tname_decl =
                                  let uu____10704 =
                                    let uu____10705 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____10737  ->
                                              match uu____10737 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____10750 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____10705,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____10750, false)
                                     in
                                  constructor_or_logic_type_decl uu____10704
                                   in
                                let uu____10759 =
                                  match vars with
                                  | [] ->
                                      let uu____10772 =
                                        let uu____10773 =
                                          let uu____10776 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____10776
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____10773
                                         in
                                      ([], uu____10772)
                                  | uu____10787 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____10796 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____10796
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____10810 =
                                          let uu____10817 =
                                            let uu____10818 =
                                              let uu____10833 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____10833)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____10818
                                             in
                                          (uu____10817,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10810
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____10759 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____10694 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____10873 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____10873 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____10891 =
                                               let uu____10892 =
                                                 let uu____10899 =
                                                   let uu____10900 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____10900
                                                    in
                                                 (uu____10899,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10892
                                                in
                                             [uu____10891]
                                           else []  in
                                         let uu____10904 =
                                           let uu____10907 =
                                             let uu____10910 =
                                               let uu____10911 =
                                                 let uu____10918 =
                                                   let uu____10919 =
                                                     let uu____10930 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____10930)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10919
                                                    in
                                                 (uu____10918,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10911
                                                in
                                             [uu____10910]  in
                                           FStar_List.append karr uu____10907
                                            in
                                         FStar_List.append decls1 uu____10904
                                      in
                                   let aux =
                                     let uu____10946 =
                                       let uu____10949 =
                                         inversion_axioms tapp vars  in
                                       let uu____10952 =
                                         let uu____10955 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____10955]  in
                                       FStar_List.append uu____10949
                                         uu____10952
                                        in
                                     FStar_List.append kindingAx uu____10946
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____10962,uu____10963,uu____10964,uu____10965,uu____10966)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____10974,t,uu____10976,n_tps,uu____10978) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____10986 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____10986 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11026 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11026 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11047 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11047 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11061 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11061 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11131 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11131,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11133 =
                                  let uu____11152 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11152, true)
                                   in
                                FStar_All.pipe_right uu____11133
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
                              let uu____11191 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11191 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11203::uu____11204 ->
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
                                         let uu____11249 =
                                           let uu____11260 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11260)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____11249
                                     | uu____11285 -> tok_typing  in
                                   let uu____11294 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11294 with
                                    | (vars',guards',env'',decls_formals,uu____11319)
                                        ->
                                        let uu____11332 =
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
                                        (match uu____11332 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11363 ->
                                                   let uu____11370 =
                                                     let uu____11371 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11371
                                                      in
                                                   [uu____11370]
                                                in
                                             let encode_elim uu____11383 =
                                               let uu____11384 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11384 with
                                               | (head1,args) ->
                                                   let uu____11427 =
                                                     let uu____11428 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11428.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11427 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11438;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11439;_},uu____11440)
                                                        ->
                                                        let uu____11445 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11445
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11458
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11458
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
                                                                    uu____11507
                                                                    ->
                                                                    let uu____11508
                                                                    =
                                                                    let uu____11513
                                                                    =
                                                                    let uu____11514
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11514
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11513)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11508
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11530
                                                                    =
                                                                    let uu____11531
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11531
                                                                     in
                                                                    if
                                                                    uu____11530
                                                                    then
                                                                    let uu____11544
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11544]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11546
                                                                    =
                                                                    let uu____11559
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11609
                                                                     ->
                                                                    fun
                                                                    uu____11610
                                                                     ->
                                                                    match 
                                                                    (uu____11609,
                                                                    uu____11610)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____11705
                                                                    =
                                                                    let uu____11712
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____11712
                                                                     in
                                                                    (match uu____11705
                                                                    with
                                                                    | 
                                                                    (uu____11725,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____11733
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____11733
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____11735
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____11735
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
                                                                    uu____11559
                                                                     in
                                                                  (match uu____11546
                                                                   with
                                                                   | 
                                                                   (uu____11750,arg_vars,elim_eqns_or_guards,uu____11753)
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
                                                                    let uu____11781
                                                                    =
                                                                    let uu____11788
                                                                    =
                                                                    let uu____11789
                                                                    =
                                                                    let uu____11800
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____11811
                                                                    =
                                                                    let uu____11812
                                                                    =
                                                                    let uu____11817
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____11817)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11812
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11800,
                                                                    uu____11811)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11789
                                                                     in
                                                                    (uu____11788,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11781
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____11835
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____11835
                                                                    then
                                                                    let x =
                                                                    let uu____11841
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____11841,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____11843
                                                                    =
                                                                    let uu____11850
                                                                    =
                                                                    let uu____11851
                                                                    =
                                                                    let uu____11862
                                                                    =
                                                                    let uu____11867
                                                                    =
                                                                    let uu____11870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____11870]
                                                                     in
                                                                    [uu____11867]
                                                                     in
                                                                    let uu____11875
                                                                    =
                                                                    let uu____11876
                                                                    =
                                                                    let uu____11881
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____11882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____11881,
                                                                    uu____11882)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11876
                                                                     in
                                                                    (uu____11862,
                                                                    [x],
                                                                    uu____11875)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11851
                                                                     in
                                                                    let uu____11901
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____11850,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____11901)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11843
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____11908
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
                                                                    (let uu____11936
                                                                    =
                                                                    let uu____11937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____11937
                                                                    dapp1  in
                                                                    [uu____11936])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____11908
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____11944
                                                                    =
                                                                    let uu____11951
                                                                    =
                                                                    let uu____11952
                                                                    =
                                                                    let uu____11963
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____11974
                                                                    =
                                                                    let uu____11975
                                                                    =
                                                                    let uu____11980
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____11980)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11975
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11963,
                                                                    uu____11974)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11952
                                                                     in
                                                                    (uu____11951,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11944)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12000 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12000
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12013
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12013
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
                                                                    uu____12062
                                                                    ->
                                                                    let uu____12063
                                                                    =
                                                                    let uu____12068
                                                                    =
                                                                    let uu____12069
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12069
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12068)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12063
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12085
                                                                    =
                                                                    let uu____12086
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12086
                                                                     in
                                                                    if
                                                                    uu____12085
                                                                    then
                                                                    let uu____12099
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12099]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12101
                                                                    =
                                                                    let uu____12114
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12164
                                                                     ->
                                                                    fun
                                                                    uu____12165
                                                                     ->
                                                                    match 
                                                                    (uu____12164,
                                                                    uu____12165)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12260
                                                                    =
                                                                    let uu____12267
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12267
                                                                     in
                                                                    (match uu____12260
                                                                    with
                                                                    | 
                                                                    (uu____12280,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12288
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12288
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12290
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12290
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
                                                                    uu____12114
                                                                     in
                                                                  (match uu____12101
                                                                   with
                                                                   | 
                                                                   (uu____12305,arg_vars,elim_eqns_or_guards,uu____12308)
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
                                                                    let uu____12336
                                                                    =
                                                                    let uu____12343
                                                                    =
                                                                    let uu____12344
                                                                    =
                                                                    let uu____12355
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12366
                                                                    =
                                                                    let uu____12367
                                                                    =
                                                                    let uu____12372
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12372)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12367
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12355,
                                                                    uu____12366)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12344
                                                                     in
                                                                    (uu____12343,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12336
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12390
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12390
                                                                    then
                                                                    let x =
                                                                    let uu____12396
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12396,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12398
                                                                    =
                                                                    let uu____12405
                                                                    =
                                                                    let uu____12406
                                                                    =
                                                                    let uu____12417
                                                                    =
                                                                    let uu____12422
                                                                    =
                                                                    let uu____12425
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12425]
                                                                     in
                                                                    [uu____12422]
                                                                     in
                                                                    let uu____12430
                                                                    =
                                                                    let uu____12431
                                                                    =
                                                                    let uu____12436
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12437
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12436,
                                                                    uu____12437)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12431
                                                                     in
                                                                    (uu____12417,
                                                                    [x],
                                                                    uu____12430)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12406
                                                                     in
                                                                    let uu____12456
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12405,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12456)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12398
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12463
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
                                                                    (let uu____12491
                                                                    =
                                                                    let uu____12492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12492
                                                                    dapp1  in
                                                                    [uu____12491])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12463
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12499
                                                                    =
                                                                    let uu____12506
                                                                    =
                                                                    let uu____12507
                                                                    =
                                                                    let uu____12518
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12529
                                                                    =
                                                                    let uu____12530
                                                                    =
                                                                    let uu____12535
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12535)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12530
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12518,
                                                                    uu____12529)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12507
                                                                     in
                                                                    (uu____12506,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12499)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____12554 ->
                                                        ((let uu____12556 =
                                                            let uu____12561 =
                                                              let uu____12562
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____12563
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____12562
                                                                uu____12563
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____12561)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____12556);
                                                         ([], [])))
                                                in
                                             let uu____12568 = encode_elim ()
                                                in
                                             (match uu____12568 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____12588 =
                                                      let uu____12591 =
                                                        let uu____12594 =
                                                          let uu____12597 =
                                                            let uu____12600 =
                                                              let uu____12601
                                                                =
                                                                let uu____12612
                                                                  =
                                                                  let uu____12615
                                                                    =
                                                                    let uu____12616
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____12616
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12615
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____12612)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____12601
                                                               in
                                                            [uu____12600]  in
                                                          let uu____12621 =
                                                            let uu____12624 =
                                                              let uu____12627
                                                                =
                                                                let uu____12630
                                                                  =
                                                                  let uu____12633
                                                                    =
                                                                    let uu____12636
                                                                    =
                                                                    let uu____12639
                                                                    =
                                                                    let uu____12640
                                                                    =
                                                                    let uu____12647
                                                                    =
                                                                    let uu____12648
                                                                    =
                                                                    let uu____12659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12659)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12648
                                                                     in
                                                                    (uu____12647,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12640
                                                                     in
                                                                    let uu____12672
                                                                    =
                                                                    let uu____12675
                                                                    =
                                                                    let uu____12676
                                                                    =
                                                                    let uu____12683
                                                                    =
                                                                    let uu____12684
                                                                    =
                                                                    let uu____12695
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____12706
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____12695,
                                                                    uu____12706)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12684
                                                                     in
                                                                    (uu____12683,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12676
                                                                     in
                                                                    [uu____12675]
                                                                     in
                                                                    uu____12639
                                                                    ::
                                                                    uu____12672
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____12636
                                                                     in
                                                                  FStar_List.append
                                                                    uu____12633
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____12630
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____12627
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____12624
                                                             in
                                                          FStar_List.append
                                                            uu____12597
                                                            uu____12621
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____12594
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____12591
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____12588
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
           (fun uu____12752  ->
              fun se  ->
                match uu____12752 with
                | (g,env1) ->
                    let uu____12772 = encode_sigelt env1 se  in
                    (match uu____12772 with
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
      let encode_binding b uu____12837 =
        match uu____12837 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____12869 ->
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
                 ((let uu____12875 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____12875
                   then
                     let uu____12876 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____12877 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____12878 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____12876 uu____12877 uu____12878
                   else ());
                  (let uu____12880 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____12880 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12896 =
                         let uu____12903 =
                           let uu____12904 =
                             let uu____12905 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____12905
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____12904  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____12903
                          in
                       (match uu____12896 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____12921 = FStar_Options.log_queries ()
                                 in
                              if uu____12921
                              then
                                let uu____12924 =
                                  let uu____12925 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____12926 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____12927 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____12925 uu____12926 uu____12927
                                   in
                                FStar_Pervasives_Native.Some uu____12924
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____12943,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____12957 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____12957 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____12980,se,uu____12982) ->
                 let uu____12987 = encode_sigelt env1 se  in
                 (match uu____12987 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____13004,se) ->
                 let uu____13010 = encode_sigelt env1 se  in
                 (match uu____13010 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13027 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13027 with | (uu____13050,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13065 'Auu____13066 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13065,'Auu____13066)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13135  ->
              match uu____13135 with
              | (l,uu____13147,uu____13148) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13194  ->
              match uu____13194 with
              | (l,uu____13208,uu____13209) ->
                  let uu____13218 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13219 =
                    let uu____13222 =
                      let uu____13223 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13223  in
                    [uu____13222]  in
                  uu____13218 :: uu____13219))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13250 =
      let uu____13253 =
        let uu____13254 = FStar_Util.psmap_empty ()  in
        let uu____13269 = FStar_Util.psmap_empty ()  in
        let uu____13272 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13275 =
          let uu____13276 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13276 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13254;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13269;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13272;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13275;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13253]  in
    FStar_ST.op_Colon_Equals last_env uu____13250
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13314 = FStar_ST.op_Bang last_env  in
      match uu____13314 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13345 ->
          let uu___94_13348 = e  in
          let uu____13349 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___94_13348.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___94_13348.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___94_13348.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___94_13348.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___94_13348.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___94_13348.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___94_13348.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___94_13348.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13349;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___94_13348.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13355 = FStar_ST.op_Bang last_env  in
    match uu____13355 with
    | [] -> failwith "Empty env stack"
    | uu____13385::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13420  ->
    let uu____13421 = FStar_ST.op_Bang last_env  in
    match uu____13421 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
        let top =
          let uu___95_13459 = hd1  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___95_13459.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___95_13459.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___95_13459.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___95_13459.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___95_13459.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = refs;
            FStar_SMTEncoding_Env.nolabels =
              (uu___95_13459.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___95_13459.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___95_13459.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___95_13459.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___95_13459.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13491  ->
    let uu____13492 = FStar_ST.op_Bang last_env  in
    match uu____13492 with
    | [] -> failwith "Popping an empty stack"
    | uu____13522::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____13604::uu____13605,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___96_13613 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___96_13613.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___96_13613.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___96_13613.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____13614 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____13633 =
        let uu____13636 =
          let uu____13637 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____13637  in
        let uu____13638 = open_fact_db_tags env  in uu____13636 ::
          uu____13638
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____13633
  
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
      let uu____13664 = encode_sigelt env se  in
      match uu____13664 with
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
        let uu____13706 = FStar_Options.log_queries ()  in
        if uu____13706
        then
          let uu____13709 =
            let uu____13710 =
              let uu____13711 =
                let uu____13712 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____13712 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____13711  in
            FStar_SMTEncoding_Term.Caption uu____13710  in
          uu____13709 :: decls
        else decls  in
      (let uu____13723 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13723
       then
         let uu____13724 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____13724
       else ());
      (let env =
         let uu____13727 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____13727 tcenv  in
       let uu____13728 = encode_top_level_facts env se  in
       match uu____13728 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____13742 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____13742)))
  
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
      (let uu____13758 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13758
       then
         let uu____13759 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____13759
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____13798  ->
                 fun se  ->
                   match uu____13798 with
                   | (g,env2) ->
                       let uu____13818 = encode_top_level_facts env2 se  in
                       (match uu____13818 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____13841 =
         encode_signature
           (let uu___97_13850 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___97_13850.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___97_13850.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___97_13850.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___97_13850.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___97_13850.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___97_13850.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___97_13850.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___97_13850.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___97_13850.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___97_13850.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____13841 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____13869 = FStar_Options.log_queries ()  in
             if uu____13869
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___98_13877 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___98_13877.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___98_13877.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___98_13877.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___98_13877.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___98_13877.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___98_13877.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___98_13877.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___98_13877.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___98_13877.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___98_13877.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____13879 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____13879
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
        (let uu____13937 =
           let uu____13938 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____13938.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____13937);
        (let env =
           let uu____13940 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____13940 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____13952 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____13989 = aux rest  in
                 (match uu____13989 with
                  | (out,rest1) ->
                      let t =
                        let uu____14019 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14019 with
                        | FStar_Pervasives_Native.Some uu____14024 ->
                            let uu____14025 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14025
                              x.FStar_Syntax_Syntax.sort
                        | uu____14026 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14030 =
                        let uu____14033 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___99_14036 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___99_14036.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___99_14036.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14033 :: out  in
                      (uu____14030, rest1))
             | uu____14041 -> ([], bindings1)  in
           let uu____14048 = aux bindings  in
           match uu____14048 with
           | (closing,bindings1) ->
               let uu____14073 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14073, bindings1)
            in
         match uu____13952 with
         | (q1,bindings1) ->
             let uu____14096 =
               let uu____14101 =
                 FStar_List.filter
                   (fun uu___81_14106  ->
                      match uu___81_14106 with
                      | FStar_TypeChecker_Env.Binding_sig uu____14107 ->
                          false
                      | uu____14114 -> true) bindings1
                  in
               encode_env_bindings env uu____14101  in
             (match uu____14096 with
              | (env_decls,env1) ->
                  ((let uu____14132 =
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
                    if uu____14132
                    then
                      let uu____14133 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14133
                    else ());
                   (let uu____14135 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14135 with
                    | (phi,qdecls) ->
                        let uu____14156 =
                          let uu____14161 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14161 phi
                           in
                        (match uu____14156 with
                         | (labels,phi1) ->
                             let uu____14178 = encode_labels labels  in
                             (match uu____14178 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14215 =
                                      let uu____14222 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14223 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14222,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14223)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14215
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
  