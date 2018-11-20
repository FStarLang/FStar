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
                let mk_macro_name s =
                  Prims.strcat FStar_Ident.reserved_prefix s  in
                let mk_op_and rng vname =
                  let uu____515 =
                    let uu____528 =
                      let uu____550 =
                        let uu____551 =
                          let uu____552 =
                            let uu____557 =
                              FStar_SMTEncoding_Term.unboxBool x  in
                            let uu____558 =
                              FStar_SMTEncoding_Term.unboxBool y  in
                            (uu____557, uu____558)  in
                          FStar_SMTEncoding_Util.mkAnd uu____552  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____551
                         in
                      quant xy uu____550  in
                    uu____528 rng vname  in
                  match uu____515 with
                  | (uu____571,tok,arity,decls) ->
                      let macro_name = mk_macro_name vname  in
                      let macro =
                        let uu____586 =
                          let uu____605 =
                            let uu____606 =
                              let uu____614 =
                                let uu____617 =
                                  let uu____620 =
                                    let uu____621 =
                                      let uu____628 =
                                        FStar_SMTEncoding_Term.unboxBool x
                                         in
                                      let uu____629 =
                                        FStar_SMTEncoding_Term.boxBool
                                          FStar_SMTEncoding_Util.mkFalse
                                         in
                                      (uu____628, y, uu____629)  in
                                    FStar_SMTEncoding_Util.mkITE uu____621
                                     in
                                  [uu____620]  in
                                x :: uu____617  in
                              (vname, uu____614)  in
                            FStar_SMTEncoding_Util.mkApp uu____606  in
                          (macro_name, xy, FStar_SMTEncoding_Term.Term_sort,
                            uu____605,
                            (FStar_Pervasives_Native.Some "&& macro"))
                           in
                        FStar_SMTEncoding_Term.mkDefineFun uu____586  in
                      ((mk_macro_name vname), tok, arity,
                        (FStar_List.append decls [macro]))
                   in
                let mk_op_or rng vname =
                  let uu____672 =
                    let uu____685 =
                      let uu____707 =
                        let uu____708 =
                          let uu____709 =
                            let uu____714 =
                              FStar_SMTEncoding_Term.unboxBool x  in
                            let uu____715 =
                              FStar_SMTEncoding_Term.unboxBool y  in
                            (uu____714, uu____715)  in
                          FStar_SMTEncoding_Util.mkOr uu____709  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____708
                         in
                      quant xy uu____707  in
                    uu____685 rng vname  in
                  match uu____672 with
                  | (uu____728,tok,arity,decls) ->
                      let macro_name = mk_macro_name vname  in
                      let macro =
                        let uu____743 =
                          let uu____762 =
                            let uu____763 =
                              let uu____771 =
                                let uu____774 =
                                  let uu____777 =
                                    let uu____778 =
                                      let uu____785 =
                                        let uu____786 =
                                          FStar_SMTEncoding_Term.unboxBool x
                                           in
                                        FStar_SMTEncoding_Util.mkNot
                                          uu____786
                                         in
                                      let uu____787 =
                                        FStar_SMTEncoding_Term.boxBool
                                          FStar_SMTEncoding_Util.mkTrue
                                         in
                                      (uu____785, y, uu____787)  in
                                    FStar_SMTEncoding_Util.mkITE uu____778
                                     in
                                  [uu____777]  in
                                x :: uu____774  in
                              (vname, uu____771)  in
                            FStar_SMTEncoding_Util.mkApp uu____763  in
                          (macro_name, xy, FStar_SMTEncoding_Term.Term_sort,
                            uu____762,
                            (FStar_Pervasives_Native.Some "|| macro"))
                           in
                        FStar_SMTEncoding_Term.mkDefineFun uu____743  in
                      (macro_name, tok, arity,
                        (FStar_List.append decls [macro]))
                   in
                let prims1 =
                  let uu____831 =
                    let uu____855 =
                      let uu____877 =
                        let uu____878 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____878
                         in
                      quant axy uu____877  in
                    (FStar_Parser_Const.op_Eq, uu____855)  in
                  let uu____898 =
                    let uu____924 =
                      let uu____948 =
                        let uu____970 =
                          let uu____971 =
                            let uu____972 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____972  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____971
                           in
                        quant axy uu____970  in
                      (FStar_Parser_Const.op_notEq, uu____948)  in
                    let uu____992 =
                      let uu____1018 =
                        let uu____1042 =
                          let uu____1064 =
                            let uu____1065 =
                              let uu____1066 =
                                let uu____1071 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____1072 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____1071, uu____1072)  in
                              FStar_SMTEncoding_Util.mkLT uu____1066  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1065
                             in
                          quant xy uu____1064  in
                        (FStar_Parser_Const.op_LT, uu____1042)  in
                      let uu____1092 =
                        let uu____1118 =
                          let uu____1142 =
                            let uu____1164 =
                              let uu____1165 =
                                let uu____1166 =
                                  let uu____1171 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____1172 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____1171, uu____1172)  in
                                FStar_SMTEncoding_Util.mkLTE uu____1166  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1165
                               in
                            quant xy uu____1164  in
                          (FStar_Parser_Const.op_LTE, uu____1142)  in
                        let uu____1192 =
                          let uu____1218 =
                            let uu____1242 =
                              let uu____1264 =
                                let uu____1265 =
                                  let uu____1266 =
                                    let uu____1271 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____1272 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____1271, uu____1272)  in
                                  FStar_SMTEncoding_Util.mkGT uu____1266  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1265
                                 in
                              quant xy uu____1264  in
                            (FStar_Parser_Const.op_GT, uu____1242)  in
                          let uu____1292 =
                            let uu____1318 =
                              let uu____1342 =
                                let uu____1364 =
                                  let uu____1365 =
                                    let uu____1366 =
                                      let uu____1371 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1372 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1371, uu____1372)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1366
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1365
                                   in
                                quant xy uu____1364  in
                              (FStar_Parser_Const.op_GTE, uu____1342)  in
                            let uu____1392 =
                              let uu____1418 =
                                let uu____1442 =
                                  let uu____1464 =
                                    let uu____1465 =
                                      let uu____1466 =
                                        let uu____1471 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1472 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1471, uu____1472)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1466
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1465
                                     in
                                  quant xy uu____1464  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1442)
                                 in
                              let uu____1492 =
                                let uu____1518 =
                                  let uu____1542 =
                                    let uu____1564 =
                                      let uu____1565 =
                                        let uu____1566 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1566
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1565
                                       in
                                    quant qx uu____1564  in
                                  (FStar_Parser_Const.op_Minus, uu____1542)
                                   in
                                let uu____1586 =
                                  let uu____1612 =
                                    let uu____1636 =
                                      let uu____1658 =
                                        let uu____1659 =
                                          let uu____1660 =
                                            let uu____1665 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1666 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1665, uu____1666)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1660
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1659
                                         in
                                      quant xy uu____1658  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1636)
                                     in
                                  let uu____1686 =
                                    let uu____1712 =
                                      let uu____1736 =
                                        let uu____1758 =
                                          let uu____1759 =
                                            let uu____1760 =
                                              let uu____1765 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1766 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1765, uu____1766)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1760
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1759
                                           in
                                        quant xy uu____1758  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1736)
                                       in
                                    let uu____1786 =
                                      let uu____1812 =
                                        let uu____1836 =
                                          let uu____1858 =
                                            let uu____1859 =
                                              let uu____1860 =
                                                let uu____1865 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1866 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1865, uu____1866)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1860
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1859
                                             in
                                          quant xy uu____1858  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1836)
                                         in
                                      let uu____1886 =
                                        let uu____1912 =
                                          let uu____1936 =
                                            let uu____1958 =
                                              let uu____1959 =
                                                let uu____1960 =
                                                  let uu____1965 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1966 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1965, uu____1966)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1960
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1959
                                               in
                                            quant xy uu____1958  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1936)
                                           in
                                        let uu____1986 =
                                          let uu____2012 =
                                            let uu____2038 =
                                              let uu____2064 =
                                                let uu____2088 =
                                                  let uu____2110 =
                                                    let uu____2111 =
                                                      let uu____2112 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____2112
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____2111
                                                     in
                                                  quant qx uu____2110  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____2088)
                                                 in
                                              [uu____2064]  in
                                            (FStar_Parser_Const.op_Or,
                                              mk_op_or) :: uu____2038
                                             in
                                          (FStar_Parser_Const.op_And,
                                            mk_op_and) :: uu____2012
                                           in
                                        uu____1912 :: uu____1986  in
                                      uu____1812 :: uu____1886  in
                                    uu____1712 :: uu____1786  in
                                  uu____1612 :: uu____1686  in
                                uu____1518 :: uu____1586  in
                              uu____1418 :: uu____1492  in
                            uu____1318 :: uu____1392  in
                          uu____1218 :: uu____1292  in
                        uu____1118 :: uu____1192  in
                      uu____1018 :: uu____1092  in
                    uu____924 :: uu____992  in
                  uu____831 :: uu____898  in
                let mk1 l v1 =
                  let uu____2563 =
                    let uu____2578 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2680  ->
                              match uu____2680 with
                              | (l',uu____2704) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2578
                      (FStar_Option.map
                         (fun uu____2821  ->
                            match uu____2821 with
                            | (uu____2855,b) ->
                                let uu____2895 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2895 v1))
                     in
                  FStar_All.pipe_right uu____2563 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2993  ->
                          match uu____2993 with
                          | (l',uu____3017) -> FStar_Ident.lid_equals l l'))
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
          let uu____3091 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3091 with
          | (xxsym,xx) ->
              let uu____3102 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3102 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3118 =
                     let uu____3126 =
                       let uu____3127 =
                         let uu____3138 =
                           let uu____3139 =
                             let uu____3144 =
                               let uu____3145 =
                                 let uu____3150 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3150)  in
                               FStar_SMTEncoding_Util.mkEq uu____3145  in
                             (xx_has_type, uu____3144)  in
                           FStar_SMTEncoding_Util.mkImp uu____3139  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____3138)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____3127  in
                     let uu____3175 =
                       let uu____3177 =
                         let uu____3179 =
                           let uu____3181 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____3181  in
                         Prims.strcat module_name uu____3179  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3177
                        in
                     (uu____3126, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3175)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3118)
  
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
    let uu____3273 = f env.FStar_SMTEncoding_Env.tcenv s t  in
    (uu____3273, env)  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3293 =
      let uu____3294 =
        let uu____3302 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3302, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3294  in
    let uu____3307 =
      let uu____3310 =
        let uu____3311 =
          let uu____3319 =
            let uu____3320 =
              let uu____3331 =
                let uu____3332 =
                  let uu____3337 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3337)  in
                FStar_SMTEncoding_Util.mkImp uu____3332  in
              ([[typing_pred]], [xx], uu____3331)  in
            let uu____3356 =
              let uu____3371 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3371  in
            uu____3356 uu____3320  in
          (uu____3319, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3311  in
      [uu____3310]  in
    uu____3293 :: uu____3307  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3404 =
      let uu____3405 =
        let uu____3413 =
          let uu____3414 = FStar_TypeChecker_Env.get_range env  in
          let uu____3415 =
            let uu____3426 =
              let uu____3431 =
                let uu____3434 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3434]  in
              [uu____3431]  in
            let uu____3439 =
              let uu____3440 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3440 tt  in
            (uu____3426, [bb], uu____3439)  in
          FStar_SMTEncoding_Term.mkForall uu____3414 uu____3415  in
        (uu____3413, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3405  in
    let uu____3459 =
      let uu____3462 =
        let uu____3463 =
          let uu____3471 =
            let uu____3472 =
              let uu____3483 =
                let uu____3484 =
                  let uu____3489 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3489)  in
                FStar_SMTEncoding_Util.mkImp uu____3484  in
              ([[typing_pred]], [xx], uu____3483)  in
            let uu____3510 =
              let uu____3525 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3525  in
            uu____3510 uu____3472  in
          (uu____3471, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3463  in
      [uu____3462]  in
    uu____3404 :: uu____3459  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3549 =
        let uu____3555 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____3555, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____3549  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3579 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3579  in
    let uu____3584 =
      let uu____3585 =
        let uu____3593 =
          let uu____3594 = FStar_TypeChecker_Env.get_range env  in
          let uu____3595 =
            let uu____3606 =
              let uu____3611 =
                let uu____3614 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3614]  in
              [uu____3611]  in
            let uu____3619 =
              let uu____3620 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3620 tt  in
            (uu____3606, [bb], uu____3619)  in
          FStar_SMTEncoding_Term.mkForall uu____3594 uu____3595  in
        (uu____3593, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3585  in
    let uu____3639 =
      let uu____3642 =
        let uu____3643 =
          let uu____3651 =
            let uu____3652 =
              let uu____3663 =
                let uu____3664 =
                  let uu____3669 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3669)  in
                FStar_SMTEncoding_Util.mkImp uu____3664  in
              ([[typing_pred]], [xx], uu____3663)  in
            let uu____3690 =
              let uu____3705 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3705  in
            uu____3690 uu____3652  in
          (uu____3651, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3643  in
      let uu____3710 =
        let uu____3713 =
          let uu____3714 =
            let uu____3722 =
              let uu____3723 =
                let uu____3734 =
                  let uu____3735 =
                    let uu____3740 =
                      let uu____3741 =
                        let uu____3744 =
                          let uu____3747 =
                            let uu____3750 =
                              let uu____3751 =
                                let uu____3756 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3757 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3756, uu____3757)  in
                              FStar_SMTEncoding_Util.mkGT uu____3751  in
                            let uu____3759 =
                              let uu____3762 =
                                let uu____3763 =
                                  let uu____3768 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3769 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3768, uu____3769)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3763  in
                              let uu____3771 =
                                let uu____3774 =
                                  let uu____3775 =
                                    let uu____3780 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3781 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3780, uu____3781)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3775  in
                                [uu____3774]  in
                              uu____3762 :: uu____3771  in
                            uu____3750 :: uu____3759  in
                          typing_pred_y :: uu____3747  in
                        typing_pred :: uu____3744  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3741  in
                    (uu____3740, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3735  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3734)
                 in
              let uu____3805 =
                let uu____3820 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3820  in
              uu____3805 uu____3723  in
            (uu____3722,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3714  in
        [uu____3713]  in
      uu____3642 :: uu____3710  in
    uu____3584 :: uu____3639  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3853 =
      let uu____3854 =
        let uu____3862 =
          let uu____3863 = FStar_TypeChecker_Env.get_range env  in
          let uu____3864 =
            let uu____3875 =
              let uu____3880 =
                let uu____3883 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3883]  in
              [uu____3880]  in
            let uu____3888 =
              let uu____3889 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3889 tt  in
            (uu____3875, [bb], uu____3888)  in
          FStar_SMTEncoding_Term.mkForall uu____3863 uu____3864  in
        (uu____3862, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3854  in
    let uu____3908 =
      let uu____3911 =
        let uu____3912 =
          let uu____3920 =
            let uu____3921 =
              let uu____3932 =
                let uu____3933 =
                  let uu____3938 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3938)  in
                FStar_SMTEncoding_Util.mkImp uu____3933  in
              ([[typing_pred]], [xx], uu____3932)  in
            let uu____3959 =
              let uu____3974 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3974  in
            uu____3959 uu____3921  in
          (uu____3920, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3912  in
      [uu____3911]  in
    uu____3853 :: uu____3908  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____4002 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____4002]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____4030 =
      let uu____4031 =
        let uu____4039 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____4039, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4031  in
    [uu____4030]  in
  let mk_macro_name s = Prims.strcat FStar_Ident.reserved_prefix s  in
  let bind_macro env lid macro_name =
    let fvb = FStar_SMTEncoding_Env.lookup_lid env lid  in
    FStar_SMTEncoding_Env.push_free_var env lid
      fvb.FStar_SMTEncoding_Env.smt_arity macro_name
      fvb.FStar_SMTEncoding_Env.smt_token
     in
  let mk_and_interp env conj uu____4092 =
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
      let uu____4134 =
        let uu____4153 =
          let uu____4154 =
            let uu____4162 =
              let uu____4165 =
                let uu____4168 =
                  FStar_SMTEncoding_Util.mkITE
                    (valid_a, b, FStar_SMTEncoding_Term.mk_Witness_term)
                   in
                [uu____4168]  in
              a :: uu____4165  in
            (conj, uu____4162)  in
          FStar_SMTEncoding_Util.mkApp uu____4154  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4153,
          (FStar_Pervasives_Native.Some "macro for embedded conjunction"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4134  in
    let uu____4197 =
      let uu____4198 =
        let uu____4199 =
          let uu____4207 =
            let uu____4208 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4209 =
              let uu____4220 =
                let uu____4221 =
                  let uu____4226 =
                    FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                  (uu____4226, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____4221  in
              ([[l_and_a_b]], [aa; bb], uu____4220)  in
            FStar_SMTEncoding_Term.mkForall uu____4208 uu____4209  in
          (uu____4207, (FStar_Pervasives_Native.Some "/\\ interpretation"),
            "l_and-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4199  in
      [uu____4198; macro]  in
    let uu____4254 = bind_macro env FStar_Parser_Const.and_lid macro_name  in
    (uu____4197, uu____4254)  in
  let mk_or_interp env disj uu____4275 =
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
      let uu____4317 =
        let uu____4336 =
          let uu____4337 =
            let uu____4345 =
              let uu____4348 =
                let uu____4351 =
                  let uu____4352 =
                    let uu____4359 = FStar_SMTEncoding_Util.mkNot valid_a  in
                    (uu____4359, b, FStar_SMTEncoding_Term.mk_Witness_term)
                     in
                  FStar_SMTEncoding_Util.mkITE uu____4352  in
                [uu____4351]  in
              a :: uu____4348  in
            (disj, uu____4345)  in
          FStar_SMTEncoding_Util.mkApp uu____4337  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4336,
          (FStar_Pervasives_Native.Some "macro for embedded disjunction"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4317  in
    let uu____4388 =
      let uu____4389 =
        let uu____4390 =
          let uu____4398 =
            let uu____4399 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4400 =
              let uu____4411 =
                let uu____4412 =
                  let uu____4417 =
                    FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                  (uu____4417, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____4412  in
              ([[l_or_a_b]], [aa; bb], uu____4411)  in
            FStar_SMTEncoding_Term.mkForall uu____4399 uu____4400  in
          (uu____4398, (FStar_Pervasives_Native.Some "\\/ interpretation"),
            "l_or-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4390  in
      [uu____4389; macro]  in
    let uu____4445 = bind_macro env FStar_Parser_Const.or_lid macro_name  in
    (uu____4388, uu____4445)  in
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
      let uu____4508 =
        let uu____4527 =
          let uu____4528 =
            let uu____4536 =
              let uu____4539 =
                let uu____4542 =
                  FStar_SMTEncoding_Util.mkITE
                    (valid_a, b, FStar_SMTEncoding_Term.mk_Witness_term)
                   in
                [uu____4542]  in
              a :: uu____4539  in
            (imp, uu____4536)  in
          FStar_SMTEncoding_Util.mkApp uu____4528  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4527,
          (FStar_Pervasives_Native.Some "macro for embedded implication"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4508  in
    let uu____4571 =
      let uu____4572 =
        let uu____4573 =
          let uu____4581 =
            let uu____4582 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4583 =
              let uu____4594 =
                let uu____4595 =
                  let uu____4600 =
                    FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                  (uu____4600, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____4595  in
              ([[l_imp_a_b]], [aa; bb], uu____4594)  in
            FStar_SMTEncoding_Term.mkForall uu____4582 uu____4583  in
          (uu____4581, (FStar_Pervasives_Native.Some "==> interpretation"),
            "l_imp-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4573  in
      [uu____4572; macro]  in
    let uu____4628 = bind_macro env FStar_Parser_Const.imp_lid macro_name  in
    (uu____4571, uu____4628)  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____4684 =
      let uu____4685 =
        let uu____4693 =
          let uu____4694 = FStar_TypeChecker_Env.get_range env  in
          let uu____4695 =
            let uu____4706 =
              let uu____4707 =
                let uu____4712 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4712, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4707  in
            ([[l_iff_a_b]], [aa; bb], uu____4706)  in
          FStar_SMTEncoding_Term.mkForall uu____4694 uu____4695  in
        (uu____4693, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4685  in
    [uu____4684]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4777 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4777  in
    let uu____4782 =
      let uu____4783 =
        let uu____4791 =
          let uu____4792 = FStar_TypeChecker_Env.get_range env  in
          let uu____4793 =
            let uu____4804 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4804)  in
          FStar_SMTEncoding_Term.mkForall uu____4792 uu____4793  in
        (uu____4791, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4783  in
    [uu____4782]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____4881 =
      let uu____4882 =
        let uu____4890 =
          let uu____4891 = FStar_TypeChecker_Env.get_range env  in
          let uu____4892 =
            let uu____4903 =
              let uu____4904 =
                let uu____4909 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4909, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4904  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4903)  in
          FStar_SMTEncoding_Term.mkForall uu____4891 uu____4892  in
        (uu____4890, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4882  in
    [uu____4881]  in
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
    let uu____5005 =
      let uu____5006 =
        let uu____5014 =
          let uu____5015 = FStar_TypeChecker_Env.get_range env  in
          let uu____5016 =
            let uu____5027 =
              let uu____5028 =
                let uu____5033 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5033, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5028  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5027)  in
          FStar_SMTEncoding_Term.mkForall uu____5015 uu____5016  in
        (uu____5014, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5006  in
    [uu____5005]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____5093 =
      let uu____5094 =
        let uu____5102 =
          let uu____5103 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5103 range_ty  in
        let uu____5104 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____5102, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5104)
         in
      FStar_SMTEncoding_Util.mkAssume uu____5094  in
    [uu____5093]  in
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
        let uu____5158 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5158 x1 t  in
      let uu____5160 = FStar_TypeChecker_Env.get_range env  in
      let uu____5161 =
        let uu____5172 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____5172)  in
      FStar_SMTEncoding_Term.mkForall uu____5160 uu____5161  in
    let uu____5191 =
      let uu____5192 =
        let uu____5200 =
          let uu____5201 = FStar_TypeChecker_Env.get_range env  in
          let uu____5202 =
            let uu____5213 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____5213)  in
          FStar_SMTEncoding_Term.mkForall uu____5201 uu____5202  in
        (uu____5200,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5192  in
    [uu____5191]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____5276 =
      let uu____5277 =
        let uu____5285 =
          let uu____5286 = FStar_TypeChecker_Env.get_range env  in
          let uu____5287 =
            let uu____5303 =
              let uu____5304 =
                let uu____5309 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____5310 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____5309, uu____5310)  in
              FStar_SMTEncoding_Util.mkAnd uu____5304  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____5303)
             in
          FStar_SMTEncoding_Term.mkForall' uu____5286 uu____5287  in
        (uu____5285,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5277  in
    [uu____5276]  in
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
          let uu____5967 =
            FStar_Util.find_opt
              (fun uu____6013  ->
                 match uu____6013 with
                 | (l,uu____6033) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5967 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____6094,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____6167 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____6167 with
        | (form,decls) ->
            let uu____6176 =
              let uu____6179 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____6179]  in
            FStar_List.append decls uu____6176
  
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
              let uu____6236 =
                ((let uu____6240 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6240) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6236
              then
                let arg_sorts =
                  let uu____6254 =
                    let uu____6255 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6255.FStar_Syntax_Syntax.n  in
                  match uu____6254 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6261) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6299  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6306 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6308 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6308 with
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
                (let uu____6350 = prims.is lid  in
                 if uu____6350
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6361 = prims.mk lid vname  in
                   match uu____6361 with
                   | (vname1,tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname1 (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6401 =
                      let uu____6420 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6420 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6448 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6448
                            then
                              let uu____6453 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___380_6456 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___380_6456.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___380_6456.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___380_6456.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___380_6456.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___380_6456.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___380_6456.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___380_6456.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___380_6456.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___380_6456.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___380_6456.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___380_6456.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___380_6456.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___380_6456.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___380_6456.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___380_6456.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___380_6456.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___380_6456.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___380_6456.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___380_6456.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___380_6456.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___380_6456.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___380_6456.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___380_6456.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___380_6456.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___380_6456.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___380_6456.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___380_6456.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___380_6456.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___380_6456.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___380_6456.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___380_6456.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___380_6456.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___380_6456.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___380_6456.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___380_6456.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___380_6456.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___380_6456.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___380_6456.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___380_6456.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___380_6456.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___380_6456.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___380_6456.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6453
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6479 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6479)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6401 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6560 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6560 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6594 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___370_6655  ->
                                       match uu___370_6655 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6659 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6659 with
                                            | (uu____6683,(xxsym,uu____6685))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6709 =
                                                  let uu____6710 =
                                                    let uu____6718 =
                                                      let uu____6719 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6720 =
                                                        let uu____6731 =
                                                          let uu____6732 =
                                                            let uu____6737 =
                                                              let uu____6738
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6738
                                                               in
                                                            (vapp,
                                                              uu____6737)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6732
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6731)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6719 uu____6720
                                                       in
                                                    (uu____6718,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6710
                                                   in
                                                [uu____6709])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6753 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6753 with
                                            | (uu____6777,(xxsym,uu____6779))
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
                                                let uu____6811 =
                                                  let uu____6812 =
                                                    let uu____6820 =
                                                      let uu____6821 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6822 =
                                                        let uu____6833 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6833)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6821 uu____6822
                                                       in
                                                    (uu____6820,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6812
                                                   in
                                                [uu____6811])
                                       | uu____6846 -> []))
                                in
                             let uu____6847 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6847 with
                              | (vars,guards,env',decls1,uu____6874) ->
                                  let uu____6887 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6900 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6900, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6904 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6904 with
                                         | (g,ds) ->
                                             let uu____6917 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6917,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6887 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6934 =
                                           let uu____6942 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6942)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6934
                                          in
                                       let uu____6948 =
                                         let vname_decl =
                                           let uu____6956 =
                                             let uu____6968 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6988  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6968,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6956
                                            in
                                         let uu____6999 =
                                           let env2 =
                                             let uu___381_7005 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___381_7005.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____7006 =
                                             let uu____7008 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____7008  in
                                           if uu____7006
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6999 with
                                         | (tok_typing,decls2) ->
                                             let uu____7025 =
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
                                                   let uu____7049 =
                                                     let uu____7050 =
                                                       let uu____7053 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____7053
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____7050
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____7049)
                                               | uu____7063 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____7078 =
                                                       let uu____7086 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____7086]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____7078
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____7108 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____7109 =
                                                       let uu____7120 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____7120)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____7108 uu____7109
                                                      in
                                                   let name_tok_corr =
                                                     let uu____7130 =
                                                       let uu____7138 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____7138,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____7130
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
                                                       let uu____7177 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7178 =
                                                         let uu____7189 =
                                                           let uu____7190 =
                                                             let uu____7195 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____7196 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____7195,
                                                               uu____7196)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____7190
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____7189)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7177
                                                         uu____7178
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
                                             (match uu____7025 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6948 with
                                        | (decls2,env2) ->
                                            let uu____7247 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____7257 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____7257 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____7272 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____7272,
                                                    decls)
                                               in
                                            (match uu____7247 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____7289 =
                                                     let uu____7297 =
                                                       let uu____7298 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7299 =
                                                         let uu____7310 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____7310)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7298
                                                         uu____7299
                                                        in
                                                     (uu____7297,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7289
                                                    in
                                                 let freshness =
                                                   let uu____7326 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____7326
                                                   then
                                                     let uu____7334 =
                                                       let uu____7335 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7336 =
                                                         let uu____7349 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____7367 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____7349,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____7367)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____7335
                                                         uu____7336
                                                        in
                                                     let uu____7373 =
                                                       let uu____7376 =
                                                         let uu____7377 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____7377 env2
                                                           vapp vars
                                                          in
                                                       [uu____7376]  in
                                                     uu____7334 :: uu____7373
                                                   else []  in
                                                 let g =
                                                   let uu____7383 =
                                                     let uu____7386 =
                                                       let uu____7389 =
                                                         let uu____7392 =
                                                           let uu____7395 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____7395
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____7392
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____7389
                                                        in
                                                     FStar_List.append decls2
                                                       uu____7386
                                                      in
                                                   FStar_List.append decls11
                                                     uu____7383
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
          let uu____7437 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7437 with
          | FStar_Pervasives_Native.None  ->
              let uu____7448 = encode_free_var false env x t t_norm []  in
              (match uu____7448 with
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
            let uu____7519 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7519 with
            | (decls,env1) ->
                let uu____7538 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7538
                then
                  let uu____7547 =
                    let uu____7550 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7550  in
                  (uu____7547, env1)
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
             (fun uu____7610  ->
                fun lb  ->
                  match uu____7610 with
                  | (decls,env1) ->
                      let uu____7630 =
                        let uu____7637 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7637
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7630 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7670 = FStar_Syntax_Util.head_and_args t  in
    match uu____7670 with
    | (hd1,args) ->
        let uu____7714 =
          let uu____7715 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7715.FStar_Syntax_Syntax.n  in
        (match uu____7714 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7721,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7745 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7756 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___382_7764 = en  in
    let uu____7765 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___382_7764.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___382_7764.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___382_7764.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___382_7764.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___382_7764.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7765;
      FStar_SMTEncoding_Env.nolabels =
        (uu___382_7764.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___382_7764.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___382_7764.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___382_7764.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___382_7764.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7797  ->
      fun quals  ->
        match uu____7797 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7904 = FStar_Util.first_N nbinders formals  in
              match uu____7904 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____8005  ->
                         fun uu____8006  ->
                           match (uu____8005, uu____8006) with
                           | ((formal,uu____8032),(binder,uu____8034)) ->
                               let uu____8055 =
                                 let uu____8062 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____8062)  in
                               FStar_Syntax_Syntax.NT uu____8055) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____8076 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8117  ->
                              match uu____8117 with
                              | (x,i) ->
                                  let uu____8136 =
                                    let uu___383_8137 = x  in
                                    let uu____8138 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_8137.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_8137.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8138
                                    }  in
                                  (uu____8136, i)))
                       in
                    FStar_All.pipe_right uu____8076
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____8162 =
                      let uu____8167 = FStar_Syntax_Subst.compress body  in
                      let uu____8168 =
                        let uu____8169 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____8169
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____8167 uu____8168
                       in
                    uu____8162 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____8254 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____8254
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___384_8261 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___384_8261.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___384_8261.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___384_8261.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___384_8261.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___384_8261.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___384_8261.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___384_8261.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___384_8261.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___384_8261.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___384_8261.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___384_8261.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___384_8261.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___384_8261.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___384_8261.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___384_8261.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___384_8261.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___384_8261.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___384_8261.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___384_8261.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___384_8261.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___384_8261.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___384_8261.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___384_8261.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___384_8261.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___384_8261.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___384_8261.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___384_8261.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___384_8261.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___384_8261.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___384_8261.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___384_8261.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___384_8261.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___384_8261.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___384_8261.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___384_8261.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___384_8261.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___384_8261.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___384_8261.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___384_8261.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___384_8261.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___384_8261.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___384_8261.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____8311 = FStar_Syntax_Util.abs_formals e  in
                match uu____8311 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8393::uu____8394 ->
                         let uu____8415 =
                           let uu____8416 =
                             let uu____8419 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____8419
                              in
                           uu____8416.FStar_Syntax_Syntax.n  in
                         (match uu____8415 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8477 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8477 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____8534 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____8534
                                   then
                                     let uu____8580 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8580 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8701  ->
                                                   fun uu____8702  ->
                                                     match (uu____8701,
                                                             uu____8702)
                                                     with
                                                     | ((x,uu____8728),
                                                        (b,uu____8730)) ->
                                                         let uu____8751 =
                                                           let uu____8758 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8758)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8751)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8766 =
                                            let uu____8795 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8795)  in
                                          (uu____8766, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8894 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8894 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____9067) ->
                              let uu____9072 =
                                let uu____9101 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____9101  in
                              (uu____9072, true)
                          | uu____9194 when Prims.op_Negation norm1 ->
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
                          | uu____9197 ->
                              let uu____9198 =
                                let uu____9200 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____9202 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____9200 uu____9202
                                 in
                              failwith uu____9198)
                     | uu____9238 ->
                         let rec aux' t_norm2 =
                           let uu____9278 =
                             let uu____9279 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____9279.FStar_Syntax_Syntax.n  in
                           match uu____9278 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____9337 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____9337 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____9380 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____9380 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____9507) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____9512 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___386_9584  ->
                  match () with
                  | () ->
                      let uu____9591 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9591
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9607 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9670  ->
                                   fun lb  ->
                                     match uu____9670 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9725 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9725
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9731 =
                                             let uu____9740 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9740
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9731 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9607 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9870 =
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
                               | uu____9883 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9893 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9893 vars)
                                   else
                                     (let uu____9896 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9896)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9957;
                                    FStar_Syntax_Syntax.lbeff = uu____9958;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9960;
                                    FStar_Syntax_Syntax.lbpos = uu____9961;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9985 =
                                     let uu____9994 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9994 with
                                     | (tcenv',uu____10012,e_t) ->
                                         let uu____10018 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10035 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10018 with
                                          | (e1,t_norm1) ->
                                              ((let uu___387_10062 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___387_10062.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9985 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10076 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____10076 with
                                         | ((binders,body,uu____10098,t_body),curry)
                                             ->
                                             ((let uu____10112 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10112
                                               then
                                                 let uu____10117 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10120 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10117 uu____10120
                                               else ());
                                              (let uu____10125 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10125 with
                                               | (vars,guards,env'1,binder_decls,uu____10152)
                                                   ->
                                                   let body1 =
                                                     let uu____10166 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____10166
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
                                                     let uu____10190 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____10190
                                                       curry fvb vars
                                                      in
                                                   let uu____10191 =
                                                     let is_logical =
                                                       let uu____10204 =
                                                         let uu____10205 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____10205.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____10204 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____10211 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____10215 =
                                                         let uu____10216 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____10216
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____10215
                                                         (fun lid  ->
                                                            let uu____10225 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____10225
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____10226 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____10226
                                                     then
                                                       let uu____10242 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____10243 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____10242,
                                                         uu____10243)
                                                     else
                                                       (let uu____10254 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____10254))
                                                      in
                                                   (match uu____10191 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____10278 =
                                                            let uu____10286 =
                                                              let uu____10287
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____10288
                                                                =
                                                                let uu____10299
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____10299)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____10287
                                                                uu____10288
                                                               in
                                                            let uu____10308 =
                                                              let uu____10309
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____10309
                                                               in
                                                            (uu____10286,
                                                              uu____10308,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____10278
                                                           in
                                                        let uu____10315 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____10315
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
                               | uu____10336 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10401 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____10401,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10407 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10460  ->
                                         fun fvb  ->
                                           match uu____10460 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10515 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10515
                                                  in
                                               let gtok =
                                                 let uu____10519 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10519
                                                  in
                                               let env4 =
                                                 let uu____10522 =
                                                   let uu____10525 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10525
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10522
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10407 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10652
                                     t_norm uu____10654 =
                                     match (uu____10652, uu____10654) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10686;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10687;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10689;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10690;_})
                                         ->
                                         let uu____10717 =
                                           let uu____10726 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10726 with
                                           | (tcenv',uu____10744,e_t) ->
                                               let uu____10750 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10767 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10750 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___388_10794 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___388_10794.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10717 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10813 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10813
                                                then
                                                  let uu____10818 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10820 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10822 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10818 uu____10820
                                                    uu____10822
                                                else ());
                                               (let uu____10827 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10827 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10867 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10867
                                                      then
                                                        let uu____10872 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10875 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10877 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10880 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10872
                                                          uu____10875
                                                          uu____10877
                                                          uu____10880
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10890 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10890 with
                                                      | (vars,guards,env'1,binder_decls,uu____10921)
                                                          ->
                                                          let decl_g =
                                                            let uu____10935 =
                                                              let uu____10947
                                                                =
                                                                let uu____10950
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10950
                                                                 in
                                                              (g,
                                                                uu____10947,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10935
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
                                                            let uu____10970 =
                                                              let uu____10978
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10978)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10970
                                                             in
                                                          let gsapp =
                                                            let uu____10985 =
                                                              let uu____10993
                                                                =
                                                                let uu____10996
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10996
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10993)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10985
                                                             in
                                                          let gmax =
                                                            let uu____11005 =
                                                              let uu____11013
                                                                =
                                                                let uu____11016
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____11016
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____11013)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____11005
                                                             in
                                                          let body1 =
                                                            let uu____11025 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____11025
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____11030 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____11030
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____11048
                                                                   =
                                                                   let uu____11056
                                                                    =
                                                                    let uu____11057
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11058
                                                                    =
                                                                    let uu____11074
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
                                                                    uu____11074)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11057
                                                                    uu____11058
                                                                     in
                                                                   let uu____11088
                                                                    =
                                                                    let uu____11089
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11089
                                                                     in
                                                                   (uu____11056,
                                                                    uu____11088,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____11048
                                                                  in
                                                               let eqn_f =
                                                                 let uu____11096
                                                                   =
                                                                   let uu____11104
                                                                    =
                                                                    let uu____11105
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11106
                                                                    =
                                                                    let uu____11117
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11117)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11105
                                                                    uu____11106
                                                                     in
                                                                   (uu____11104,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____11096
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____11131
                                                                   =
                                                                   let uu____11139
                                                                    =
                                                                    let uu____11140
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11141
                                                                    =
                                                                    let uu____11152
                                                                    =
                                                                    let uu____11153
                                                                    =
                                                                    let uu____11158
                                                                    =
                                                                    let uu____11159
                                                                    =
                                                                    let uu____11167
                                                                    =
                                                                    let uu____11170
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11170
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____11167)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____11159
                                                                     in
                                                                    (gsapp,
                                                                    uu____11158)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11153
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11152)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11140
                                                                    uu____11141
                                                                     in
                                                                   (uu____11139,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____11131
                                                                  in
                                                               let uu____11187
                                                                 =
                                                                 let uu____11196
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____11196
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____11225)
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
                                                                    let uu____11247
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11247
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____11249
                                                                    =
                                                                    let uu____11257
                                                                    =
                                                                    let uu____11258
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11259
                                                                    =
                                                                    let uu____11270
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11270)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11258
                                                                    uu____11259
                                                                     in
                                                                    (uu____11257,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11249
                                                                     in
                                                                    let uu____11283
                                                                    =
                                                                    let uu____11292
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____11292
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11307
                                                                    =
                                                                    let uu____11310
                                                                    =
                                                                    let uu____11311
                                                                    =
                                                                    let uu____11319
                                                                    =
                                                                    let uu____11320
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11321
                                                                    =
                                                                    let uu____11332
                                                                    =
                                                                    let uu____11333
                                                                    =
                                                                    let uu____11338
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____11338,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11333
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11332)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11320
                                                                    uu____11321
                                                                     in
                                                                    (uu____11319,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11311
                                                                     in
                                                                    [uu____11310]
                                                                     in
                                                                    (d3,
                                                                    uu____11307)
                                                                     in
                                                                    (match uu____11283
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
                                                               (match uu____11187
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
                                   let uu____11401 =
                                     let uu____11414 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11477  ->
                                          fun uu____11478  ->
                                            match (uu____11477, uu____11478)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11603 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11603 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11414
                                      in
                                   (match uu____11401 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11676 =
                                          let isDeclFun uu___371_11691 =
                                            match uu___371_11691 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11693 -> true
                                            | uu____11706 -> false  in
                                          let uu____11708 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11708
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11676 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11748 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___372_11754  ->
                                        match uu___372_11754 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11757 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11765 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11765)))
                                in
                             if uu____11748
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___390_11787  ->
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
                   let uu____11825 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11825
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
        let uu____11895 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11895 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11901 = encode_sigelt' env se  in
      match uu____11901 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11913 =
                  let uu____11914 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11914  in
                [uu____11913]
            | uu____11917 ->
                let uu____11918 =
                  let uu____11921 =
                    let uu____11922 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11922  in
                  uu____11921 :: g  in
                let uu____11925 =
                  let uu____11928 =
                    let uu____11929 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11929  in
                  [uu____11928]  in
                FStar_List.append uu____11918 uu____11925
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
        let uu____11945 =
          let uu____11946 = FStar_Syntax_Subst.compress t  in
          uu____11946.FStar_Syntax_Syntax.n  in
        match uu____11945 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11951)) -> s = "opaque_to_smt"
        | uu____11956 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11965 =
          let uu____11966 = FStar_Syntax_Subst.compress t  in
          uu____11966.FStar_Syntax_Syntax.n  in
        match uu____11965 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11971)) -> s = "uninterpreted_by_smt"
        | uu____11976 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11982 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11988 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____12000 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____12001 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12002 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____12015 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12017 =
            let uu____12019 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____12019  in
          if uu____12017
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12048 ->
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
               let uu____12080 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____12080 with
               | (formals,uu____12100) ->
                   let arity = FStar_List.length formals  in
                   let uu____12124 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____12124 with
                    | (aname,atok,env2) ->
                        let uu____12150 =
                          let uu____12155 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____12155 env2
                           in
                        (match uu____12150 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12167 =
                                 let uu____12168 =
                                   let uu____12180 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12200  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____12180,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____12168
                                  in
                               [uu____12167;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____12217 =
                               let aux uu____12278 uu____12279 =
                                 match (uu____12278, uu____12279) with
                                 | ((bv,uu____12338),(env3,acc_sorts,acc)) ->
                                     let uu____12385 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____12385 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____12217 with
                              | (uu____12469,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____12495 =
                                      let uu____12503 =
                                        let uu____12504 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12505 =
                                          let uu____12516 =
                                            let uu____12517 =
                                              let uu____12522 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____12522)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12517
                                             in
                                          ([[app]], xs_sorts, uu____12516)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12504 uu____12505
                                         in
                                      (uu____12503,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12495
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
                                    let uu____12539 =
                                      let uu____12547 =
                                        let uu____12548 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12549 =
                                          let uu____12560 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12560)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12548 uu____12549
                                         in
                                      (uu____12547,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12539
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12575 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12575 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12601,uu____12602)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12603 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12603 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12625,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12632 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___373_12638  ->
                      match uu___373_12638 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12641 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12647 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12650 -> false))
               in
            Prims.op_Negation uu____12632  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12660 =
               let uu____12667 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12667 env fv t quals  in
             match uu____12660 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12686 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12686 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12706 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12706 with
           | (uvs,f1) ->
               let env1 =
                 let uu___391_12718 = env  in
                 let uu____12719 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___391_12718.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___391_12718.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___391_12718.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12719;
                   FStar_SMTEncoding_Env.warn =
                     (uu___391_12718.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___391_12718.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___391_12718.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___391_12718.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___391_12718.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___391_12718.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___391_12718.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12721 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12721 with
                | (f3,decls) ->
                    let g =
                      let uu____12735 =
                        let uu____12736 =
                          let uu____12744 =
                            let uu____12745 =
                              let uu____12747 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12747
                               in
                            FStar_Pervasives_Native.Some uu____12745  in
                          let uu____12751 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12744, uu____12751)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12736  in
                      [uu____12735]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12756) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12770 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12792 =
                       let uu____12795 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12795.FStar_Syntax_Syntax.fv_name  in
                     uu____12792.FStar_Syntax_Syntax.v  in
                   let uu____12796 =
                     let uu____12798 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12798  in
                   if uu____12796
                   then
                     let val_decl =
                       let uu___392_12830 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___392_12830.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___392_12830.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___392_12830.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12831 = encode_sigelt' env1 val_decl  in
                     match uu____12831 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12770 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12867,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12869;
                          FStar_Syntax_Syntax.lbtyp = uu____12870;
                          FStar_Syntax_Syntax.lbeff = uu____12871;
                          FStar_Syntax_Syntax.lbdef = uu____12872;
                          FStar_Syntax_Syntax.lbattrs = uu____12873;
                          FStar_Syntax_Syntax.lbpos = uu____12874;_}::[]),uu____12875)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12894 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12894 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12937 =
                   let uu____12940 =
                     let uu____12941 =
                       let uu____12949 =
                         let uu____12950 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12951 =
                           let uu____12962 =
                             let uu____12963 =
                               let uu____12968 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12968)  in
                             FStar_SMTEncoding_Util.mkEq uu____12963  in
                           ([[b2t_x]], [xx], uu____12962)  in
                         FStar_SMTEncoding_Term.mkForall uu____12950
                           uu____12951
                          in
                       (uu____12949,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12941  in
                   [uu____12940]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12937
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13000,uu____13001) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___374_13011  ->
                  match uu___374_13011 with
                  | FStar_Syntax_Syntax.Discriminator uu____13013 -> true
                  | uu____13015 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13017,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13029 =
                     let uu____13031 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13031.FStar_Ident.idText  in
                   uu____13029 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___375_13038  ->
                     match uu___375_13038 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13041 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13044) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___376_13058  ->
                  match uu___376_13058 with
                  | FStar_Syntax_Syntax.Projector uu____13060 -> true
                  | uu____13066 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13070 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____13070 with
           | FStar_Pervasives_Native.Some uu____13077 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___393_13079 = se  in
                 let uu____13080 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13080;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___393_13079.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___393_13079.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___393_13079.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13083) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13098) ->
          let uu____13107 = encode_sigelts env ses  in
          (match uu____13107 with
           | (g,env1) ->
               let uu____13124 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___377_13147  ->
                         match uu___377_13147 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13149;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13150;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13151;_}
                             -> false
                         | uu____13158 -> true))
                  in
               (match uu____13124 with
                | (g',inversions) ->
                    let uu____13174 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___378_13195  ->
                              match uu___378_13195 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13197 ->
                                  true
                              | uu____13210 -> false))
                       in
                    (match uu____13174 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13227,tps,k,uu____13230,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___379_13249  ->
                    match uu___379_13249 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13253 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13266 = c  in
              match uu____13266 with
              | (name,args,uu____13271,uu____13272,uu____13273) ->
                  let uu____13284 =
                    let uu____13285 =
                      let uu____13297 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13324  ->
                                match uu____13324 with
                                | (uu____13333,sort,uu____13335) -> sort))
                         in
                      (name, uu____13297, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13285  in
                  [uu____13284]
            else
              (let uu____13346 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____13346 c)
             in
          let inversion_axioms tapp vars =
            let uu____13374 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13382 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____13382 FStar_Option.isNone))
               in
            if uu____13374
            then []
            else
              (let uu____13417 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____13417 with
               | (xxsym,xx) ->
                   let uu____13430 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13469  ->
                             fun l  ->
                               match uu____13469 with
                               | (out,decls) ->
                                   let uu____13489 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____13489 with
                                    | (uu____13500,data_t) ->
                                        let uu____13502 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13502 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13546 =
                                                 let uu____13547 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13547.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13546 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13550,indices) ->
                                                   indices
                                               | uu____13576 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13606  ->
                                                         match uu____13606
                                                         with
                                                         | (x,uu____13614) ->
                                                             let uu____13619
                                                               =
                                                               let uu____13620
                                                                 =
                                                                 let uu____13628
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13628,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13620
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13619)
                                                    env)
                                                in
                                             let uu____13633 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13633 with
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
                                                      let uu____13663 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13681
                                                                 =
                                                                 let uu____13686
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13686,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13681)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13663
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13689 =
                                                      let uu____13690 =
                                                        let uu____13695 =
                                                          let uu____13696 =
                                                            let uu____13701 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13701,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13696
                                                           in
                                                        (out, uu____13695)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13690
                                                       in
                                                    (uu____13689,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13430 with
                    | (data_ax,decls) ->
                        let uu____13714 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13714 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13731 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13731 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13738 =
                                 let uu____13746 =
                                   let uu____13747 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13748 =
                                     let uu____13759 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13772 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13759,
                                       uu____13772)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13747 uu____13748
                                    in
                                 let uu____13781 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13746,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13781)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13738
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13787 =
            let uu____13792 =
              let uu____13793 = FStar_Syntax_Subst.compress k  in
              uu____13793.FStar_Syntax_Syntax.n  in
            match uu____13792 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13828 -> (tps, k)  in
          (match uu____13787 with
           | (formals,res) ->
               let uu____13835 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13835 with
                | (formals1,res1) ->
                    let uu____13846 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13846 with
                     | (vars,guards,env',binder_decls,uu____13871) ->
                         let arity = FStar_List.length vars  in
                         let uu____13885 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13885 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13915 =
                                  let uu____13923 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13923)  in
                                FStar_SMTEncoding_Util.mkApp uu____13915  in
                              let uu____13929 =
                                let tname_decl =
                                  let uu____13939 =
                                    let uu____13940 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13968  ->
                                              match uu____13968 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13989 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13940,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13989, false)
                                     in
                                  constructor_or_logic_type_decl uu____13939
                                   in
                                let uu____13997 =
                                  match vars with
                                  | [] ->
                                      let uu____14010 =
                                        let uu____14011 =
                                          let uu____14014 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____14014
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____14011
                                         in
                                      ([], uu____14010)
                                  | uu____14026 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14036 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14036
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14052 =
                                          let uu____14060 =
                                            let uu____14061 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____14062 =
                                              let uu____14078 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____14078)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____14061 uu____14062
                                             in
                                          (uu____14060,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14052
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13997 with
                                | (tok_decls,env2) ->
                                    let uu____14105 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____14105
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13929 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14133 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____14133 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14155 =
                                               let uu____14156 =
                                                 let uu____14164 =
                                                   let uu____14165 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14165
                                                    in
                                                 (uu____14164,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14156
                                                in
                                             [uu____14155]
                                           else []  in
                                         let uu____14173 =
                                           let uu____14176 =
                                             let uu____14179 =
                                               let uu____14180 =
                                                 let uu____14188 =
                                                   let uu____14189 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____14190 =
                                                     let uu____14201 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14201)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____14189 uu____14190
                                                    in
                                                 (uu____14188,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14180
                                                in
                                             [uu____14179]  in
                                           FStar_List.append karr uu____14176
                                            in
                                         FStar_List.append decls1 uu____14173
                                      in
                                   let aux =
                                     let uu____14216 =
                                       let uu____14219 =
                                         inversion_axioms tapp vars  in
                                       let uu____14222 =
                                         let uu____14225 =
                                           let uu____14226 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____14226 env2
                                             tapp vars
                                            in
                                         [uu____14225]  in
                                       FStar_List.append uu____14219
                                         uu____14222
                                        in
                                     FStar_List.append kindingAx uu____14216
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14231,uu____14232,uu____14233,uu____14234,uu____14235)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14243,t,uu____14245,n_tps,uu____14247) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____14257 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____14257 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____14305 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____14305 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____14333 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____14333 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14353 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____14353 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14432 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____14432,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14439 =
                                  let uu____14440 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14440, true)
                                   in
                                let uu____14448 =
                                  let uu____14455 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____14455
                                   in
                                FStar_All.pipe_right uu____14439 uu____14448
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
                              let uu____14467 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____14467 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14479::uu____14480 ->
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
                                         let uu____14539 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____14540 =
                                           let uu____14551 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14551)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____14539 uu____14540
                                     | uu____14572 -> tok_typing  in
                                   let uu____14583 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14583 with
                                    | (vars',guards',env'',decls_formals,uu____14608)
                                        ->
                                        let uu____14621 =
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
                                        (match uu____14621 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14651 ->
                                                   let uu____14660 =
                                                     let uu____14661 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14661
                                                      in
                                                   [uu____14660]
                                                in
                                             let encode_elim uu____14677 =
                                               let uu____14678 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14678 with
                                               | (head1,args) ->
                                                   let uu____14729 =
                                                     let uu____14730 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14730.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14729 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14742;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14743;_},uu____14744)
                                                        ->
                                                        let uu____14749 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14749
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14770
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14770
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
                                                                    uu____14824
                                                                    ->
                                                                    let uu____14825
                                                                    =
                                                                    let uu____14831
                                                                    =
                                                                    let uu____14833
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14833
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14831)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14825
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14853
                                                                    =
                                                                    let uu____14855
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14855
                                                                     in
                                                                    if
                                                                    uu____14853
                                                                    then
                                                                    let uu____14871
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14871]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14874
                                                                    =
                                                                    let uu____14888
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14945
                                                                     ->
                                                                    fun
                                                                    uu____14946
                                                                     ->
                                                                    match 
                                                                    (uu____14945,
                                                                    uu____14946)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15057
                                                                    =
                                                                    let uu____15065
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15065
                                                                     in
                                                                    (match uu____15057
                                                                    with
                                                                    | 
                                                                    (uu____15079,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15090
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15090
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15095
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15095
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
                                                                    uu____14888
                                                                     in
                                                                  (match uu____14874
                                                                   with
                                                                   | 
                                                                   (uu____15116,arg_vars,elim_eqns_or_guards,uu____15119)
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
                                                                    let uu____15146
                                                                    =
                                                                    let uu____15154
                                                                    =
                                                                    let uu____15155
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15156
                                                                    =
                                                                    let uu____15167
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15169
                                                                    =
                                                                    let uu____15170
                                                                    =
                                                                    let uu____15175
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15175)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15170
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15167,
                                                                    uu____15169)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15155
                                                                    uu____15156
                                                                     in
                                                                    (uu____15154,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15146
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15190
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15196,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15190
                                                                     in
                                                                    let uu____15199
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15199
                                                                    then
                                                                    let x =
                                                                    let uu____15208
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15208,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15213
                                                                    =
                                                                    let uu____15221
                                                                    =
                                                                    let uu____15222
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15223
                                                                    =
                                                                    let uu____15234
                                                                    =
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15242
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15242]
                                                                     in
                                                                    [uu____15239]
                                                                     in
                                                                    let uu____15247
                                                                    =
                                                                    let uu____15248
                                                                    =
                                                                    let uu____15253
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15253,
                                                                    uu____15255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15248
                                                                     in
                                                                    (uu____15234,
                                                                    [x],
                                                                    uu____15247)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15222
                                                                    uu____15223
                                                                     in
                                                                    let uu____15270
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15221,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15270)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15213
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15281
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
                                                                    (let uu____15319
                                                                    =
                                                                    let uu____15320
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15320
                                                                    dapp1  in
                                                                    [uu____15319])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15281
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15327
                                                                    =
                                                                    let uu____15335
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15337
                                                                    =
                                                                    let uu____15348
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15350
                                                                    =
                                                                    let uu____15351
                                                                    =
                                                                    let uu____15356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15356)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15351
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15348,
                                                                    uu____15350)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15336
                                                                    uu____15337
                                                                     in
                                                                    (uu____15335,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15327)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____15374 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____15374
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____15395
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____15395
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
                                                                    uu____15449
                                                                    ->
                                                                    let uu____15450
                                                                    =
                                                                    let uu____15456
                                                                    =
                                                                    let uu____15458
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15458
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15456)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15450
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15478
                                                                    =
                                                                    let uu____15480
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15480
                                                                     in
                                                                    if
                                                                    uu____15478
                                                                    then
                                                                    let uu____15496
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15496]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____15499
                                                                    =
                                                                    let uu____15513
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15570
                                                                     ->
                                                                    fun
                                                                    uu____15571
                                                                     ->
                                                                    match 
                                                                    (uu____15570,
                                                                    uu____15571)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15682
                                                                    =
                                                                    let uu____15690
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15690
                                                                     in
                                                                    (match uu____15682
                                                                    with
                                                                    | 
                                                                    (uu____15704,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15715
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15715
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15720
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15720
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
                                                                    uu____15513
                                                                     in
                                                                  (match uu____15499
                                                                   with
                                                                   | 
                                                                   (uu____15741,arg_vars,elim_eqns_or_guards,uu____15744)
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
                                                                    let uu____15771
                                                                    =
                                                                    let uu____15779
                                                                    =
                                                                    let uu____15780
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15781
                                                                    =
                                                                    let uu____15792
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15794
                                                                    =
                                                                    let uu____15795
                                                                    =
                                                                    let uu____15800
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15800)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15795
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15792,
                                                                    uu____15794)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15780
                                                                    uu____15781
                                                                     in
                                                                    (uu____15779,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15771
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15815
                                                                    =
                                                                    let uu____15821
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15821,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15815
                                                                     in
                                                                    let uu____15824
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15824
                                                                    then
                                                                    let x =
                                                                    let uu____15833
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15833,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15838
                                                                    =
                                                                    let uu____15846
                                                                    =
                                                                    let uu____15847
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15848
                                                                    =
                                                                    let uu____15859
                                                                    =
                                                                    let uu____15864
                                                                    =
                                                                    let uu____15867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15867]
                                                                     in
                                                                    [uu____15864]
                                                                     in
                                                                    let uu____15872
                                                                    =
                                                                    let uu____15873
                                                                    =
                                                                    let uu____15878
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15880
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15878,
                                                                    uu____15880)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15873
                                                                     in
                                                                    (uu____15859,
                                                                    [x],
                                                                    uu____15872)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15847
                                                                    uu____15848
                                                                     in
                                                                    let uu____15895
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15846,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15895)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15838
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15906
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
                                                                    (let uu____15944
                                                                    =
                                                                    let uu____15945
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15945
                                                                    dapp1  in
                                                                    [uu____15944])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15906
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15952
                                                                    =
                                                                    let uu____15960
                                                                    =
                                                                    let uu____15961
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15962
                                                                    =
                                                                    let uu____15973
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15975
                                                                    =
                                                                    let uu____15976
                                                                    =
                                                                    let uu____15981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15981)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15976
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15973,
                                                                    uu____15975)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15961
                                                                    uu____15962
                                                                     in
                                                                    (uu____15960,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15952)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15998 ->
                                                        ((let uu____16000 =
                                                            let uu____16006 =
                                                              let uu____16008
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____16010
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____16008
                                                                uu____16010
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____16006)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16000);
                                                         ([], [])))
                                                in
                                             let uu____16018 = encode_elim ()
                                                in
                                             (match uu____16018 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16044 =
                                                      let uu____16047 =
                                                        let uu____16050 =
                                                          let uu____16053 =
                                                            let uu____16056 =
                                                              let uu____16057
                                                                =
                                                                let uu____16069
                                                                  =
                                                                  let uu____16070
                                                                    =
                                                                    let uu____16072
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16072
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16070
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16069)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16057
                                                               in
                                                            [uu____16056]  in
                                                          let uu____16079 =
                                                            let uu____16082 =
                                                              let uu____16085
                                                                =
                                                                let uu____16088
                                                                  =
                                                                  let uu____16091
                                                                    =
                                                                    let uu____16094
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____16099
                                                                    =
                                                                    let uu____16102
                                                                    =
                                                                    let uu____16103
                                                                    =
                                                                    let uu____16111
                                                                    =
                                                                    let uu____16112
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16113
                                                                    =
                                                                    let uu____16124
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16124)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16112
                                                                    uu____16113
                                                                     in
                                                                    (uu____16111,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16103
                                                                     in
                                                                    let uu____16137
                                                                    =
                                                                    let uu____16140
                                                                    =
                                                                    let uu____16141
                                                                    =
                                                                    let uu____16149
                                                                    =
                                                                    let uu____16150
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16151
                                                                    =
                                                                    let uu____16162
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____16164
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16162,
                                                                    uu____16164)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16150
                                                                    uu____16151
                                                                     in
                                                                    (uu____16149,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16141
                                                                     in
                                                                    [uu____16140]
                                                                     in
                                                                    uu____16102
                                                                    ::
                                                                    uu____16137
                                                                     in
                                                                    uu____16094
                                                                    ::
                                                                    uu____16099
                                                                     in
                                                                  FStar_List.append
                                                                    uu____16091
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16088
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16085
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16082
                                                             in
                                                          FStar_List.append
                                                            uu____16053
                                                            uu____16079
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____16050
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____16047
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16044
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
           (fun uu____16202  ->
              fun se  ->
                match uu____16202 with
                | (g,env1) ->
                    let uu____16222 = encode_sigelt env1 se  in
                    (match uu____16222 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16290 =
        match uu____16290 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____16327 ->
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
                 ((let uu____16335 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____16335
                   then
                     let uu____16340 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____16342 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____16344 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16340 uu____16342 uu____16344
                   else ());
                  (let uu____16349 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____16349 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____16367 =
                         let uu____16375 =
                           let uu____16377 =
                             let uu____16379 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16379
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16377  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16375
                          in
                       (match uu____16367 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16399 = FStar_Options.log_queries ()
                                 in
                              if uu____16399
                              then
                                let uu____16402 =
                                  let uu____16404 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16406 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16408 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16404 uu____16406 uu____16408
                                   in
                                FStar_Pervasives_Native.Some uu____16402
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16432,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16452 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16452 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16479 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16479 with | (uu____16506,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____16522 'Auu____16523 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____16522 *
      'Auu____16523) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16596  ->
              match uu____16596 with
              | (l,uu____16609,uu____16610) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16661  ->
              match uu____16661 with
              | (l,uu____16676,uu____16677) ->
                  let uu____16688 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16691 =
                    let uu____16694 =
                      let uu____16695 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16695  in
                    [uu____16694]  in
                  uu____16688 :: uu____16691))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16724 =
      let uu____16727 =
        let uu____16728 = FStar_Util.psmap_empty ()  in
        let uu____16743 = FStar_Util.psmap_empty ()  in
        let uu____16746 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16750 =
          let uu____16752 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16752 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16728;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16743;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16746;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16750;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16727]  in
    FStar_ST.op_Colon_Equals last_env uu____16724
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16794 = FStar_ST.op_Bang last_env  in
      match uu____16794 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16822 ->
          let uu___394_16825 = e  in
          let uu____16826 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___394_16825.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___394_16825.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___394_16825.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___394_16825.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___394_16825.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___394_16825.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___394_16825.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___394_16825.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16826;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___394_16825.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16834 = FStar_ST.op_Bang last_env  in
    match uu____16834 with
    | [] -> failwith "Empty env stack"
    | uu____16861::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16893  ->
    let uu____16894 = FStar_ST.op_Bang last_env  in
    match uu____16894 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16954  ->
    let uu____16955 = FStar_ST.op_Bang last_env  in
    match uu____16955 with
    | [] -> failwith "Popping an empty stack"
    | uu____16982::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____17019  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____17072  ->
         let uu____17073 = snapshot_env ()  in
         match uu____17073 with
         | (env_depth,()) ->
             let uu____17095 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____17095 with
              | (varops_depth,()) ->
                  let uu____17117 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____17117 with
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
        (fun uu____17175  ->
           let uu____17176 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____17176 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____17271 = snapshot msg  in () 
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
        | (uu____17317::uu____17318,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___395_17326 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___395_17326.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___395_17326.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___395_17326.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17327 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____17347 =
        let uu____17350 =
          let uu____17351 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____17351  in
        let uu____17352 = open_fact_db_tags env  in uu____17350 ::
          uu____17352
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17347
  
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
      let uu____17379 = encode_sigelt env se  in
      match uu____17379 with
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
        let uu____17424 = FStar_Options.log_queries ()  in
        if uu____17424
        then
          let uu____17429 =
            let uu____17430 =
              let uu____17432 =
                let uu____17434 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17434 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17432  in
            FStar_SMTEncoding_Term.Caption uu____17430  in
          uu____17429 :: decls
        else decls  in
      (let uu____17453 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____17453
       then
         let uu____17456 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17456
       else ());
      (let env =
         let uu____17462 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17462 tcenv  in
       let uu____17463 = encode_top_level_facts env se  in
       match uu____17463 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17477 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17477)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17491 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17491
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17506 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____17506
          then
            let uu____17509 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17509
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17555  ->
                    fun se  ->
                      match uu____17555 with
                      | (g,env2) ->
                          let uu____17575 = encode_top_level_facts env2 se
                             in
                          (match uu____17575 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17598 =
            encode_signature
              (let uu___396_17607 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___396_17607.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___396_17607.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___396_17607.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___396_17607.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___396_17607.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___396_17607.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___396_17607.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___396_17607.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___396_17607.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___396_17607.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17598 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17627 = FStar_Options.log_queries ()  in
                if uu____17627
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
                 (let uu___397_17644 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___397_17644.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___397_17644.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___397_17644.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___397_17644.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___397_17644.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___397_17644.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___397_17644.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___397_17644.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___397_17644.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___397_17644.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17647 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17647
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
        (let uu____17712 =
           let uu____17714 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17714.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17712);
        (let env =
           let uu____17716 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17716 tcenv  in
         let uu____17717 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17756 = aux rest  in
                 (match uu____17756 with
                  | (out,rest1) ->
                      let t =
                        let uu____17784 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17784 with
                        | FStar_Pervasives_Native.Some uu____17787 ->
                            let uu____17788 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17788
                              x.FStar_Syntax_Syntax.sort
                        | uu____17789 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17793 =
                        let uu____17796 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___398_17799 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___398_17799.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___398_17799.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17796 :: out  in
                      (uu____17793, rest1))
             | uu____17804 -> ([], bindings)  in
           let uu____17811 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17811 with
           | (closing,bindings) ->
               let uu____17838 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17838, bindings)
            in
         match uu____17717 with
         | (q1,bindings) ->
             let uu____17869 = encode_env_bindings env bindings  in
             (match uu____17869 with
              | (env_decls,env1) ->
                  ((let uu____17891 =
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
                    if uu____17891
                    then
                      let uu____17898 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17898
                    else ());
                   (let uu____17903 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17903 with
                    | (phi,qdecls) ->
                        let uu____17924 =
                          let uu____17929 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17929 phi
                           in
                        (match uu____17924 with
                         | (labels,phi1) ->
                             let uu____17946 = encode_labels labels  in
                             (match uu____17946 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17983 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17983
                                    then
                                      let uu____17988 =
                                        let uu____17989 =
                                          let uu____17991 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17991
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17989
                                         in
                                      [uu____17988]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____18000 =
                                      let uu____18008 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____18009 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____18008,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____18009)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____18000
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
  