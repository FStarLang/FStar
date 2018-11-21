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
                    let uu____546 = quant xy i  in uu____546 rng vname  in
                  match uu____533 with
                  | (uu____580,tok,arity,decls) ->
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
                      let uu____958 =
                        let uu____982 =
                          let uu____1004 =
                            let uu____1005 =
                              let uu____1006 =
                                let uu____1011 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____1012 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____1011, uu____1012)  in
                              FStar_SMTEncoding_Util.mkLT uu____1006  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1005
                             in
                          quant xy uu____1004  in
                        (FStar_Parser_Const.op_LT, uu____982)  in
                      let uu____1032 =
                        let uu____1058 =
                          let uu____1082 =
                            let uu____1104 =
                              let uu____1105 =
                                let uu____1106 =
                                  let uu____1111 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____1112 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____1111, uu____1112)  in
                                FStar_SMTEncoding_Util.mkLTE uu____1106  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1105
                               in
                            quant xy uu____1104  in
                          (FStar_Parser_Const.op_LTE, uu____1082)  in
                        let uu____1132 =
                          let uu____1158 =
                            let uu____1182 =
                              let uu____1204 =
                                let uu____1205 =
                                  let uu____1206 =
                                    let uu____1211 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____1212 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____1211, uu____1212)  in
                                  FStar_SMTEncoding_Util.mkGT uu____1206  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1205
                                 in
                              quant xy uu____1204  in
                            (FStar_Parser_Const.op_GT, uu____1182)  in
                          let uu____1232 =
                            let uu____1258 =
                              let uu____1282 =
                                let uu____1304 =
                                  let uu____1305 =
                                    let uu____1306 =
                                      let uu____1311 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1312 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1311, uu____1312)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1306
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1305
                                   in
                                quant xy uu____1304  in
                              (FStar_Parser_Const.op_GTE, uu____1282)  in
                            let uu____1332 =
                              let uu____1358 =
                                let uu____1382 =
                                  let uu____1404 =
                                    let uu____1405 =
                                      let uu____1406 =
                                        let uu____1411 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1412 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1411, uu____1412)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1406
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1405
                                     in
                                  quant xy uu____1404  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1382)
                                 in
                              let uu____1432 =
                                let uu____1458 =
                                  let uu____1482 =
                                    let uu____1504 =
                                      let uu____1505 =
                                        let uu____1506 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1506
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1505
                                       in
                                    quant qx uu____1504  in
                                  (FStar_Parser_Const.op_Minus, uu____1482)
                                   in
                                let uu____1526 =
                                  let uu____1552 =
                                    let uu____1576 =
                                      let uu____1598 =
                                        let uu____1599 =
                                          let uu____1600 =
                                            let uu____1605 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1606 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1605, uu____1606)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1600
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1599
                                         in
                                      quant xy uu____1598  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1576)
                                     in
                                  let uu____1626 =
                                    let uu____1652 =
                                      let uu____1676 =
                                        let uu____1698 =
                                          let uu____1699 =
                                            let uu____1700 =
                                              let uu____1705 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1706 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1705, uu____1706)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1700
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1699
                                           in
                                        quant xy uu____1698  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1676)
                                       in
                                    let uu____1726 =
                                      let uu____1752 =
                                        let uu____1776 =
                                          let uu____1798 =
                                            let uu____1799 =
                                              let uu____1800 =
                                                let uu____1805 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1806 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1805, uu____1806)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1800
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1799
                                             in
                                          quant xy uu____1798  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1776)
                                         in
                                      let uu____1826 =
                                        let uu____1852 =
                                          let uu____1876 =
                                            let uu____1898 =
                                              let uu____1899 =
                                                let uu____1900 =
                                                  let uu____1905 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1906 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1905, uu____1906)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1900
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1899
                                               in
                                            quant xy uu____1898  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1876)
                                           in
                                        let uu____1926 =
                                          let uu____1952 =
                                            let uu____1978 =
                                              let uu____2004 =
                                                let uu____2028 =
                                                  let uu____2050 =
                                                    let uu____2051 =
                                                      let uu____2052 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____2052
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____2051
                                                     in
                                                  quant qx uu____2050  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____2028)
                                                 in
                                              [uu____2004]  in
                                            (FStar_Parser_Const.op_Or,
                                              mk_op_or) :: uu____1978
                                             in
                                          (FStar_Parser_Const.op_And,
                                            mk_op_and) :: uu____1952
                                           in
                                        uu____1852 :: uu____1926  in
                                      uu____1752 :: uu____1826  in
                                    uu____1652 :: uu____1726  in
                                  uu____1552 :: uu____1626  in
                                uu____1458 :: uu____1526  in
                              uu____1358 :: uu____1432  in
                            uu____1258 :: uu____1332  in
                          uu____1158 :: uu____1232  in
                        uu____1058 :: uu____1132  in
                      uu____958 :: uu____1032  in
                    (FStar_Parser_Const.op_notEq, mk_op_not) :: uu____932  in
                  uu____839 :: uu____906  in
                let mk1 l v1 =
                  let uu____2522 =
                    let uu____2537 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2639  ->
                              match uu____2639 with
                              | (l',uu____2663) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2537
                      (FStar_Option.map
                         (fun uu____2780  ->
                            match uu____2780 with
                            | (uu____2814,b) ->
                                let uu____2854 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2854 v1))
                     in
                  FStar_All.pipe_right uu____2522 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2952  ->
                          match uu____2952 with
                          | (l',uu____2976) -> FStar_Ident.lid_equals l l'))
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
          let uu____3050 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3050 with
          | (xxsym,xx) ->
              let uu____3061 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____3061 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____3077 =
                     let uu____3085 =
                       let uu____3086 =
                         let uu____3097 =
                           let uu____3098 =
                             let uu____3103 =
                               let uu____3104 =
                                 let uu____3109 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3109)  in
                               FStar_SMTEncoding_Util.mkEq uu____3104  in
                             (xx_has_type, uu____3103)  in
                           FStar_SMTEncoding_Util.mkImp uu____3098  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____3097)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____3086  in
                     let uu____3134 =
                       let uu____3136 =
                         let uu____3138 =
                           let uu____3140 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____3140  in
                         Prims.strcat module_name uu____3138  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3136
                        in
                     (uu____3085, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3134)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____3077)
  
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
    let uu____3232 = f env.FStar_SMTEncoding_Env.tcenv s t  in
    (uu____3232, env)  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3252 =
      let uu____3253 =
        let uu____3261 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3261, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3253  in
    let uu____3266 =
      let uu____3269 =
        let uu____3270 =
          let uu____3278 =
            let uu____3279 =
              let uu____3290 =
                let uu____3291 =
                  let uu____3296 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3296)  in
                FStar_SMTEncoding_Util.mkImp uu____3291  in
              ([[typing_pred]], [xx], uu____3290)  in
            let uu____3315 =
              let uu____3330 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3330  in
            uu____3315 uu____3279  in
          (uu____3278, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3270  in
      [uu____3269]  in
    uu____3252 :: uu____3266  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3363 =
      let uu____3364 =
        let uu____3372 =
          let uu____3373 = FStar_TypeChecker_Env.get_range env  in
          let uu____3374 =
            let uu____3385 =
              let uu____3390 =
                let uu____3393 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3393]  in
              [uu____3390]  in
            let uu____3398 =
              let uu____3399 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3399 tt  in
            (uu____3385, [bb], uu____3398)  in
          FStar_SMTEncoding_Term.mkForall uu____3373 uu____3374  in
        (uu____3372, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3364  in
    let uu____3418 =
      let uu____3421 =
        let uu____3422 =
          let uu____3430 =
            let uu____3431 =
              let uu____3442 =
                let uu____3443 =
                  let uu____3448 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3448)  in
                FStar_SMTEncoding_Util.mkImp uu____3443  in
              ([[typing_pred]], [xx], uu____3442)  in
            let uu____3469 =
              let uu____3484 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3484  in
            uu____3469 uu____3431  in
          (uu____3430, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3422  in
      [uu____3421]  in
    uu____3363 :: uu____3418  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3508 =
        let uu____3514 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____3514, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____3508  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3538 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3538  in
    let uu____3543 =
      let uu____3544 =
        let uu____3552 =
          let uu____3553 = FStar_TypeChecker_Env.get_range env  in
          let uu____3554 =
            let uu____3565 =
              let uu____3570 =
                let uu____3573 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3573]  in
              [uu____3570]  in
            let uu____3578 =
              let uu____3579 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3579 tt  in
            (uu____3565, [bb], uu____3578)  in
          FStar_SMTEncoding_Term.mkForall uu____3553 uu____3554  in
        (uu____3552, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3544  in
    let uu____3598 =
      let uu____3601 =
        let uu____3602 =
          let uu____3610 =
            let uu____3611 =
              let uu____3622 =
                let uu____3623 =
                  let uu____3628 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3628)  in
                FStar_SMTEncoding_Util.mkImp uu____3623  in
              ([[typing_pred]], [xx], uu____3622)  in
            let uu____3649 =
              let uu____3664 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3664  in
            uu____3649 uu____3611  in
          (uu____3610, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3602  in
      let uu____3669 =
        let uu____3672 =
          let uu____3673 =
            let uu____3681 =
              let uu____3682 =
                let uu____3693 =
                  let uu____3694 =
                    let uu____3699 =
                      let uu____3700 =
                        let uu____3703 =
                          let uu____3706 =
                            let uu____3709 =
                              let uu____3710 =
                                let uu____3715 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3716 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3715, uu____3716)  in
                              FStar_SMTEncoding_Util.mkGT uu____3710  in
                            let uu____3718 =
                              let uu____3721 =
                                let uu____3722 =
                                  let uu____3727 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3728 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3727, uu____3728)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3722  in
                              let uu____3730 =
                                let uu____3733 =
                                  let uu____3734 =
                                    let uu____3739 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3740 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3739, uu____3740)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3734  in
                                [uu____3733]  in
                              uu____3721 :: uu____3730  in
                            uu____3709 :: uu____3718  in
                          typing_pred_y :: uu____3706  in
                        typing_pred :: uu____3703  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3700  in
                    (uu____3699, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3694  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3693)
                 in
              let uu____3764 =
                let uu____3779 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3779  in
              uu____3764 uu____3682  in
            (uu____3681,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3673  in
        [uu____3672]  in
      uu____3601 :: uu____3669  in
    uu____3543 :: uu____3598  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3812 =
      let uu____3813 =
        let uu____3821 =
          let uu____3822 = FStar_TypeChecker_Env.get_range env  in
          let uu____3823 =
            let uu____3834 =
              let uu____3839 =
                let uu____3842 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3842]  in
              [uu____3839]  in
            let uu____3847 =
              let uu____3848 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3848 tt  in
            (uu____3834, [bb], uu____3847)  in
          FStar_SMTEncoding_Term.mkForall uu____3822 uu____3823  in
        (uu____3821, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3813  in
    let uu____3867 =
      let uu____3870 =
        let uu____3871 =
          let uu____3879 =
            let uu____3880 =
              let uu____3891 =
                let uu____3892 =
                  let uu____3897 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3897)  in
                FStar_SMTEncoding_Util.mkImp uu____3892  in
              ([[typing_pred]], [xx], uu____3891)  in
            let uu____3918 =
              let uu____3933 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3933  in
            uu____3918 uu____3880  in
          (uu____3879, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3871  in
      [uu____3870]  in
    uu____3812 :: uu____3867  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3961 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3961]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3989 =
      let uu____3990 =
        let uu____3998 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3998, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3990  in
    [uu____3989]  in
  let mk_macro_name s = Prims.strcat FStar_Ident.reserved_prefix s  in
  let mkValid t = FStar_SMTEncoding_Util.mkApp ("Valid", [t])  in
  let squash env t =
    let sq =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.squash_lid  in
    let b2t1 =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.b2t_lid  in
    let uu____4035 =
      let uu____4043 =
        let uu____4046 =
          let uu____4047 =
            let uu____4055 =
              let uu____4058 = FStar_SMTEncoding_Term.boxBool t  in
              [uu____4058]  in
            ((b2t1.FStar_SMTEncoding_Env.smt_id), uu____4055)  in
          FStar_SMTEncoding_Util.mkApp uu____4047  in
        [uu____4046]  in
      ((sq.FStar_SMTEncoding_Env.smt_id), uu____4043)  in
    FStar_SMTEncoding_Util.mkApp uu____4035  in
  let bind_macro env lid macro_name =
    let fvb = FStar_SMTEncoding_Env.lookup_lid env lid  in
    FStar_SMTEncoding_Env.push_free_var env lid
      fvb.FStar_SMTEncoding_Env.smt_arity macro_name
      fvb.FStar_SMTEncoding_Env.smt_token
     in
  let mk_unary_prop_connective conn interp env vname uu____4117 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let conn_a = FStar_SMTEncoding_Util.mkApp (vname, [a])  in
    let valid_conn_a = mkValid conn_a  in
    let valid_a = mkValid a  in
    let macro_name = mk_macro_name vname  in
    let macro =
      let uu____4143 =
        let uu____4162 =
          let uu____4163 = interp valid_a  in squash env uu____4163  in
        (macro_name, [aa], FStar_SMTEncoding_Term.Term_sort, uu____4162,
          (FStar_Pervasives_Native.Some "macro for embedded unary connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4143  in
    let uu____4184 =
      let uu____4185 =
        let uu____4186 =
          let uu____4194 =
            let uu____4195 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4196 =
              let uu____4207 =
                let uu____4208 =
                  let uu____4213 = interp valid_a  in
                  (uu____4213, valid_conn_a)  in
                FStar_SMTEncoding_Util.mkIff uu____4208  in
              ([[conn_a]], [aa], uu____4207)  in
            FStar_SMTEncoding_Term.mkForall uu____4195 uu____4196  in
          (uu____4194,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4186  in
      [uu____4185; macro]  in
    let uu____4236 = bind_macro env conn macro_name  in
    (uu____4184, uu____4236)  in
  let mk_binary_prop_connective conn interp env vname uu____4274 =
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
      let uu____4314 =
        let uu____4333 =
          let uu____4334 = interp (valid_a, valid_b)  in
          squash env uu____4334  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4333,
          (FStar_Pervasives_Native.Some "macro for embedded connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4314  in
    let uu____4360 =
      let uu____4361 =
        let uu____4362 =
          let uu____4370 =
            let uu____4371 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4372 =
              let uu____4383 =
                let uu____4384 =
                  let uu____4389 = interp (valid_a, valid_b)  in
                  (uu____4389, valid_conn_a_b)  in
                FStar_SMTEncoding_Util.mkIff uu____4384  in
              ([[conn_a_b]], [aa; bb], uu____4383)  in
            FStar_SMTEncoding_Term.mkForall uu____4371 uu____4372  in
          (uu____4370,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4362  in
      [uu____4361; macro]  in
    let uu____4417 = bind_macro env conn macro_name  in
    (uu____4360, uu____4417)  in
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
    let uu____4562 =
      let uu____4563 =
        let uu____4571 =
          let uu____4572 = FStar_TypeChecker_Env.get_range env  in
          let uu____4573 =
            let uu____4584 =
              let uu____4585 =
                let uu____4590 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4590, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4585  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4584)  in
          FStar_SMTEncoding_Term.mkForall uu____4572 uu____4573  in
        (uu____4571, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4563  in
    [uu____4562]  in
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
    let uu____4686 =
      let uu____4687 =
        let uu____4695 =
          let uu____4696 = FStar_TypeChecker_Env.get_range env  in
          let uu____4697 =
            let uu____4708 =
              let uu____4709 =
                let uu____4714 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4714, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4709  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4708)  in
          FStar_SMTEncoding_Term.mkForall uu____4696 uu____4697  in
        (uu____4695, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4687  in
    [uu____4686]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4774 =
      let uu____4775 =
        let uu____4783 =
          let uu____4784 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4784 range_ty  in
        let uu____4785 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4783, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4785)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4775  in
    [uu____4774]  in
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
        let uu____4839 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4839 x1 t  in
      let uu____4841 = FStar_TypeChecker_Env.get_range env  in
      let uu____4842 =
        let uu____4853 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4853)  in
      FStar_SMTEncoding_Term.mkForall uu____4841 uu____4842  in
    let uu____4872 =
      let uu____4873 =
        let uu____4881 =
          let uu____4882 = FStar_TypeChecker_Env.get_range env  in
          let uu____4883 =
            let uu____4894 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4894)  in
          FStar_SMTEncoding_Term.mkForall uu____4882 uu____4883  in
        (uu____4881,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4873  in
    [uu____4872]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4957 =
      let uu____4958 =
        let uu____4966 =
          let uu____4967 = FStar_TypeChecker_Env.get_range env  in
          let uu____4968 =
            let uu____4984 =
              let uu____4985 =
                let uu____4990 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4991 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4990, uu____4991)  in
              FStar_SMTEncoding_Util.mkAnd uu____4985  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4984)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4967 uu____4968  in
        (uu____4966,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4958  in
    [uu____4957]  in
  let mk_squash_interp env sq uu____5040 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_sq_a =
      let uu____5057 =
        let uu____5065 =
          let uu____5068 = FStar_SMTEncoding_Util.mkApp (sq, [a])  in
          [uu____5068]  in
        ("Valid", uu____5065)  in
      FStar_SMTEncoding_Util.mkApp uu____5057  in
    let uu____5076 =
      let uu____5077 =
        let uu____5085 =
          let uu____5086 = FStar_TypeChecker_Env.get_range env  in
          let uu____5087 =
            let uu____5098 =
              FStar_SMTEncoding_Util.mkIff (valid_sq_a, valid_a)  in
            ([[valid_sq_a]], [aa], uu____5098)  in
          FStar_SMTEncoding_Term.mkForall uu____5086 uu____5087  in
        (uu____5085,
          (FStar_Pervasives_Native.Some "valid-squash interpretation"),
          "valid-squash-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5077  in
    [uu____5076]  in
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
          let uu____5781 =
            FStar_Util.find_opt
              (fun uu____5827  ->
                 match uu____5827 with
                 | (l,uu____5847) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5781 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____5908,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5981 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5981 with
        | (form,decls) ->
            let uu____5990 =
              let uu____5993 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5993]  in
            FStar_List.append decls uu____5990
  
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
              let uu____6050 =
                ((let uu____6054 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____6054) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____6050
              then
                let arg_sorts =
                  let uu____6068 =
                    let uu____6069 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6069.FStar_Syntax_Syntax.n  in
                  match uu____6068 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6075) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6113  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6120 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6122 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6122 with
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
                (let uu____6164 = prims.is lid  in
                 if uu____6164
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6175 = prims.mk lid vname  in
                   match uu____6175 with
                   | (vname1,tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname1 (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6215 =
                      let uu____6234 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6234 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6262 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6262
                            then
                              let uu____6267 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___438_6270 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___438_6270.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___438_6270.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___438_6270.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___438_6270.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___438_6270.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___438_6270.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___438_6270.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___438_6270.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___438_6270.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___438_6270.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___438_6270.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___438_6270.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___438_6270.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___438_6270.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___438_6270.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___438_6270.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___438_6270.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___438_6270.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___438_6270.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___438_6270.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___438_6270.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___438_6270.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___438_6270.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___438_6270.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___438_6270.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___438_6270.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___438_6270.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___438_6270.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___438_6270.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___438_6270.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___438_6270.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___438_6270.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___438_6270.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___438_6270.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___438_6270.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___438_6270.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___438_6270.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___438_6270.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___438_6270.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___438_6270.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___438_6270.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___438_6270.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6267
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6293 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6293)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6215 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6374 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6374 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6408 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___428_6469  ->
                                       match uu___428_6469 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6473 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6473 with
                                            | (uu____6497,(xxsym,uu____6499))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6523 =
                                                  let uu____6524 =
                                                    let uu____6532 =
                                                      let uu____6533 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6534 =
                                                        let uu____6545 =
                                                          let uu____6546 =
                                                            let uu____6551 =
                                                              let uu____6552
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6552
                                                               in
                                                            (vapp,
                                                              uu____6551)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6546
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6545)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6533 uu____6534
                                                       in
                                                    (uu____6532,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6524
                                                   in
                                                [uu____6523])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6567 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6567 with
                                            | (uu____6591,(xxsym,uu____6593))
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
                                                let uu____6625 =
                                                  let uu____6626 =
                                                    let uu____6634 =
                                                      let uu____6635 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6636 =
                                                        let uu____6647 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6647)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6635 uu____6636
                                                       in
                                                    (uu____6634,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6626
                                                   in
                                                [uu____6625])
                                       | uu____6660 -> []))
                                in
                             let uu____6661 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6661 with
                              | (vars,guards,env',decls1,uu____6688) ->
                                  let uu____6701 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6714 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6714, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6718 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6718 with
                                         | (g,ds) ->
                                             let uu____6731 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6731,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6701 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6748 =
                                           let uu____6756 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6756)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6748
                                          in
                                       let uu____6762 =
                                         let vname_decl =
                                           let uu____6770 =
                                             let uu____6782 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6802  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6782,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6770
                                            in
                                         let uu____6813 =
                                           let env2 =
                                             let uu___439_6819 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___439_6819.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____6820 =
                                             let uu____6822 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6822  in
                                           if uu____6820
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6813 with
                                         | (tok_typing,decls2) ->
                                             let uu____6839 =
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
                                                   let uu____6863 =
                                                     let uu____6864 =
                                                       let uu____6867 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6867
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6864
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6863)
                                               | uu____6877 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6892 =
                                                       let uu____6900 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6900]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6892
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6922 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6923 =
                                                       let uu____6934 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6934)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6922 uu____6923
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6944 =
                                                       let uu____6952 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6952,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6944
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
                                                       let uu____6991 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6992 =
                                                         let uu____7003 =
                                                           let uu____7004 =
                                                             let uu____7009 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____7010 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____7009,
                                                               uu____7010)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____7004
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____7003)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6991
                                                         uu____6992
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
                                             (match uu____6839 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6762 with
                                        | (decls2,env2) ->
                                            let uu____7061 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____7071 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____7071 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____7086 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____7086,
                                                    decls)
                                               in
                                            (match uu____7061 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____7103 =
                                                     let uu____7111 =
                                                       let uu____7112 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7113 =
                                                         let uu____7124 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____7124)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7112
                                                         uu____7113
                                                        in
                                                     (uu____7111,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7103
                                                    in
                                                 let freshness =
                                                   let uu____7140 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____7140
                                                   then
                                                     let uu____7148 =
                                                       let uu____7149 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7150 =
                                                         let uu____7163 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____7181 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____7163,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____7181)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____7149
                                                         uu____7150
                                                        in
                                                     let uu____7187 =
                                                       let uu____7190 =
                                                         let uu____7191 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____7191 env2
                                                           vapp vars
                                                          in
                                                       [uu____7190]  in
                                                     uu____7148 :: uu____7187
                                                   else []  in
                                                 let g =
                                                   let uu____7197 =
                                                     let uu____7200 =
                                                       let uu____7203 =
                                                         let uu____7206 =
                                                           let uu____7209 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____7209
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____7206
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____7203
                                                        in
                                                     FStar_List.append decls2
                                                       uu____7200
                                                      in
                                                   FStar_List.append decls11
                                                     uu____7197
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
          let uu____7251 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7251 with
          | FStar_Pervasives_Native.None  ->
              let uu____7262 = encode_free_var false env x t t_norm []  in
              (match uu____7262 with
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
            let uu____7333 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7333 with
            | (decls,env1) ->
                let uu____7352 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7352
                then
                  let uu____7361 =
                    let uu____7364 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7364  in
                  (uu____7361, env1)
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
             (fun uu____7424  ->
                fun lb  ->
                  match uu____7424 with
                  | (decls,env1) ->
                      let uu____7444 =
                        let uu____7451 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7451
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7444 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7484 = FStar_Syntax_Util.head_and_args t  in
    match uu____7484 with
    | (hd1,args) ->
        let uu____7528 =
          let uu____7529 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7529.FStar_Syntax_Syntax.n  in
        (match uu____7528 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7535,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7559 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7570 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___440_7578 = en  in
    let uu____7579 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___440_7578.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___440_7578.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___440_7578.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___440_7578.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___440_7578.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7579;
      FStar_SMTEncoding_Env.nolabels =
        (uu___440_7578.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___440_7578.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___440_7578.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___440_7578.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___440_7578.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7611  ->
      fun quals  ->
        match uu____7611 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7718 = FStar_Util.first_N nbinders formals  in
              match uu____7718 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7819  ->
                         fun uu____7820  ->
                           match (uu____7819, uu____7820) with
                           | ((formal,uu____7846),(binder,uu____7848)) ->
                               let uu____7869 =
                                 let uu____7876 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7876)  in
                               FStar_Syntax_Syntax.NT uu____7869) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7890 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7931  ->
                              match uu____7931 with
                              | (x,i) ->
                                  let uu____7950 =
                                    let uu___441_7951 = x  in
                                    let uu____7952 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___441_7951.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___441_7951.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7952
                                    }  in
                                  (uu____7950, i)))
                       in
                    FStar_All.pipe_right uu____7890
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7976 =
                      let uu____7981 = FStar_Syntax_Subst.compress body  in
                      let uu____7982 =
                        let uu____7983 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7983
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7981 uu____7982
                       in
                    uu____7976 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____8068 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____8068
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___442_8075 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___442_8075.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___442_8075.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___442_8075.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___442_8075.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___442_8075.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___442_8075.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___442_8075.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___442_8075.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___442_8075.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___442_8075.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___442_8075.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___442_8075.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___442_8075.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___442_8075.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___442_8075.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___442_8075.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___442_8075.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___442_8075.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___442_8075.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___442_8075.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___442_8075.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___442_8075.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___442_8075.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___442_8075.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___442_8075.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___442_8075.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___442_8075.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___442_8075.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___442_8075.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___442_8075.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___442_8075.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___442_8075.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___442_8075.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___442_8075.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___442_8075.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___442_8075.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___442_8075.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___442_8075.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___442_8075.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___442_8075.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___442_8075.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___442_8075.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____8125 = FStar_Syntax_Util.abs_formals e  in
                match uu____8125 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8207::uu____8208 ->
                         let uu____8229 =
                           let uu____8230 =
                             let uu____8233 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____8233
                              in
                           uu____8230.FStar_Syntax_Syntax.n  in
                         (match uu____8229 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8291 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8291 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____8348 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____8348
                                   then
                                     let uu____8394 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8394 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8515  ->
                                                   fun uu____8516  ->
                                                     match (uu____8515,
                                                             uu____8516)
                                                     with
                                                     | ((x,uu____8542),
                                                        (b,uu____8544)) ->
                                                         let uu____8565 =
                                                           let uu____8572 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8572)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8565)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8580 =
                                            let uu____8609 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8609)  in
                                          (uu____8580, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8708 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8708 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8881) ->
                              let uu____8886 =
                                let uu____8915 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8915  in
                              (uu____8886, true)
                          | uu____9008 when Prims.op_Negation norm1 ->
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
                          | uu____9011 ->
                              let uu____9012 =
                                let uu____9014 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____9016 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____9014 uu____9016
                                 in
                              failwith uu____9012)
                     | uu____9052 ->
                         let rec aux' t_norm2 =
                           let uu____9092 =
                             let uu____9093 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____9093.FStar_Syntax_Syntax.n  in
                           match uu____9092 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____9151 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____9151 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____9194 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____9194 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____9321) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____9326 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___444_9398  ->
                  match () with
                  | () ->
                      let uu____9405 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9405
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9421 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9484  ->
                                   fun lb  ->
                                     match uu____9484 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9539 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9539
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9545 =
                                             let uu____9554 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9554
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9545 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9421 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9684 =
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
                               | uu____9697 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9707 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9707 vars)
                                   else
                                     (let uu____9710 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9710)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9771;
                                    FStar_Syntax_Syntax.lbeff = uu____9772;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9774;
                                    FStar_Syntax_Syntax.lbpos = uu____9775;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9799 =
                                     let uu____9808 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9808 with
                                     | (tcenv',uu____9826,e_t) ->
                                         let uu____9832 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9849 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____9832 with
                                          | (e1,t_norm1) ->
                                              ((let uu___445_9876 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___445_9876.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9799 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9890 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9890 with
                                         | ((binders,body,uu____9912,t_body),curry)
                                             ->
                                             ((let uu____9926 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9926
                                               then
                                                 let uu____9931 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9934 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9931 uu____9934
                                               else ());
                                              (let uu____9939 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9939 with
                                               | (vars,guards,env'1,binder_decls,uu____9966)
                                                   ->
                                                   let body1 =
                                                     let uu____9980 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9980
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
                                                     let uu____10004 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____10004
                                                       curry fvb vars
                                                      in
                                                   let uu____10005 =
                                                     let is_logical =
                                                       let uu____10018 =
                                                         let uu____10019 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____10019.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____10018 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____10025 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____10029 =
                                                         let uu____10030 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____10030
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____10029
                                                         (fun lid  ->
                                                            let uu____10039 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____10039
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____10040 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____10040
                                                     then
                                                       let uu____10056 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____10057 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____10056,
                                                         uu____10057)
                                                     else
                                                       (let uu____10068 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____10068))
                                                      in
                                                   (match uu____10005 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____10092 =
                                                            let uu____10100 =
                                                              let uu____10101
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____10102
                                                                =
                                                                let uu____10113
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____10113)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____10101
                                                                uu____10102
                                                               in
                                                            let uu____10122 =
                                                              let uu____10123
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____10123
                                                               in
                                                            (uu____10100,
                                                              uu____10122,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____10092
                                                           in
                                                        let uu____10129 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____10129
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
                               | uu____10150 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10215 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____10215,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10221 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10274  ->
                                         fun fvb  ->
                                           match uu____10274 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10329 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10329
                                                  in
                                               let gtok =
                                                 let uu____10333 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10333
                                                  in
                                               let env4 =
                                                 let uu____10336 =
                                                   let uu____10339 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10339
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10336
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10221 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10466
                                     t_norm uu____10468 =
                                     match (uu____10466, uu____10468) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10500;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10501;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10503;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10504;_})
                                         ->
                                         let uu____10531 =
                                           let uu____10540 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10540 with
                                           | (tcenv',uu____10558,e_t) ->
                                               let uu____10564 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10581 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10564 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___446_10608 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___446_10608.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10531 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10627 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10627
                                                then
                                                  let uu____10632 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10634 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10636 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10632 uu____10634
                                                    uu____10636
                                                else ());
                                               (let uu____10641 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10641 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10681 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10681
                                                      then
                                                        let uu____10686 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10689 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10691 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10694 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10686
                                                          uu____10689
                                                          uu____10691
                                                          uu____10694
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10704 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10704 with
                                                      | (vars,guards,env'1,binder_decls,uu____10735)
                                                          ->
                                                          let decl_g =
                                                            let uu____10749 =
                                                              let uu____10761
                                                                =
                                                                let uu____10764
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10764
                                                                 in
                                                              (g,
                                                                uu____10761,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10749
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
                                                            let uu____10784 =
                                                              let uu____10792
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10792)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10784
                                                             in
                                                          let gsapp =
                                                            let uu____10799 =
                                                              let uu____10807
                                                                =
                                                                let uu____10810
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10810
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10807)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10799
                                                             in
                                                          let gmax =
                                                            let uu____10819 =
                                                              let uu____10827
                                                                =
                                                                let uu____10830
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____10830
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10827)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10819
                                                             in
                                                          let body1 =
                                                            let uu____10839 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____10839
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10844 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10844
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10862
                                                                   =
                                                                   let uu____10870
                                                                    =
                                                                    let uu____10871
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10872
                                                                    =
                                                                    let uu____10888
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
                                                                    uu____10888)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10871
                                                                    uu____10872
                                                                     in
                                                                   let uu____10902
                                                                    =
                                                                    let uu____10903
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10903
                                                                     in
                                                                   (uu____10870,
                                                                    uu____10902,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10862
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10910
                                                                   =
                                                                   let uu____10918
                                                                    =
                                                                    let uu____10919
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10920
                                                                    =
                                                                    let uu____10931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10931)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10919
                                                                    uu____10920
                                                                     in
                                                                   (uu____10918,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10910
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10945
                                                                   =
                                                                   let uu____10953
                                                                    =
                                                                    let uu____10954
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10955
                                                                    =
                                                                    let uu____10966
                                                                    =
                                                                    let uu____10967
                                                                    =
                                                                    let uu____10972
                                                                    =
                                                                    let uu____10973
                                                                    =
                                                                    let uu____10981
                                                                    =
                                                                    let uu____10984
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10984
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10981)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10973
                                                                     in
                                                                    (gsapp,
                                                                    uu____10972)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10967
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10966)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10954
                                                                    uu____10955
                                                                     in
                                                                   (uu____10953,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10945
                                                                  in
                                                               let uu____11001
                                                                 =
                                                                 let uu____11010
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____11010
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____11039)
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
                                                                    let uu____11061
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11061
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____11063
                                                                    =
                                                                    let uu____11071
                                                                    =
                                                                    let uu____11072
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11073
                                                                    =
                                                                    let uu____11084
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11084)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11072
                                                                    uu____11073
                                                                     in
                                                                    (uu____11071,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11063
                                                                     in
                                                                    let uu____11097
                                                                    =
                                                                    let uu____11106
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____11106
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11121
                                                                    =
                                                                    let uu____11124
                                                                    =
                                                                    let uu____11125
                                                                    =
                                                                    let uu____11133
                                                                    =
                                                                    let uu____11134
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11135
                                                                    =
                                                                    let uu____11146
                                                                    =
                                                                    let uu____11147
                                                                    =
                                                                    let uu____11152
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____11152,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11147
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11146)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11134
                                                                    uu____11135
                                                                     in
                                                                    (uu____11133,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11125
                                                                     in
                                                                    [uu____11124]
                                                                     in
                                                                    (d3,
                                                                    uu____11121)
                                                                     in
                                                                    (match uu____11097
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
                                                               (match uu____11001
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
                                   let uu____11215 =
                                     let uu____11228 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11291  ->
                                          fun uu____11292  ->
                                            match (uu____11291, uu____11292)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11417 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11417 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11228
                                      in
                                   (match uu____11215 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11490 =
                                          let isDeclFun uu___429_11505 =
                                            match uu___429_11505 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11507 -> true
                                            | uu____11520 -> false  in
                                          let uu____11522 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11522
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11490 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11562 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___430_11568  ->
                                        match uu___430_11568 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11571 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11579 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11579)))
                                in
                             if uu____11562
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___448_11601  ->
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
                   let uu____11639 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11639
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
        let uu____11709 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11709 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11715 = encode_sigelt' env se  in
      match uu____11715 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11727 =
                  let uu____11728 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11728  in
                [uu____11727]
            | uu____11731 ->
                let uu____11732 =
                  let uu____11735 =
                    let uu____11736 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11736  in
                  uu____11735 :: g  in
                let uu____11739 =
                  let uu____11742 =
                    let uu____11743 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11743  in
                  [uu____11742]  in
                FStar_List.append uu____11732 uu____11739
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
        let uu____11759 =
          let uu____11760 = FStar_Syntax_Subst.compress t  in
          uu____11760.FStar_Syntax_Syntax.n  in
        match uu____11759 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11765)) -> s = "opaque_to_smt"
        | uu____11770 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11779 =
          let uu____11780 = FStar_Syntax_Subst.compress t  in
          uu____11780.FStar_Syntax_Syntax.n  in
        match uu____11779 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11785)) -> s = "uninterpreted_by_smt"
        | uu____11790 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11796 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11802 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____11814 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____11815 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11816 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11829 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11831 =
            let uu____11833 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____11833  in
          if uu____11831
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11862 ->
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
               let uu____11894 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11894 with
               | (formals,uu____11914) ->
                   let arity = FStar_List.length formals  in
                   let uu____11938 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11938 with
                    | (aname,atok,env2) ->
                        let uu____11964 =
                          let uu____11969 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11969 env2
                           in
                        (match uu____11964 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11981 =
                                 let uu____11982 =
                                   let uu____11994 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12014  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11994,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11982
                                  in
                               [uu____11981;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____12031 =
                               let aux uu____12092 uu____12093 =
                                 match (uu____12092, uu____12093) with
                                 | ((bv,uu____12152),(env3,acc_sorts,acc)) ->
                                     let uu____12199 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____12199 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____12031 with
                              | (uu____12283,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____12309 =
                                      let uu____12317 =
                                        let uu____12318 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12319 =
                                          let uu____12330 =
                                            let uu____12331 =
                                              let uu____12336 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____12336)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12331
                                             in
                                          ([[app]], xs_sorts, uu____12330)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12318 uu____12319
                                         in
                                      (uu____12317,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12309
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
                                    let uu____12353 =
                                      let uu____12361 =
                                        let uu____12362 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12363 =
                                          let uu____12374 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12374)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12362 uu____12363
                                         in
                                      (uu____12361,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12353
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12389 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12389 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12415,uu____12416)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12417 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12417 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12439,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12446 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___431_12452  ->
                      match uu___431_12452 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12455 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12461 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12464 -> false))
               in
            Prims.op_Negation uu____12446  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12474 =
               let uu____12481 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12481 env fv t quals  in
             match uu____12474 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12500 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12500 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12520 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12520 with
           | (uvs,f1) ->
               let env1 =
                 let uu___449_12532 = env  in
                 let uu____12533 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___449_12532.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___449_12532.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___449_12532.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12533;
                   FStar_SMTEncoding_Env.warn =
                     (uu___449_12532.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___449_12532.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___449_12532.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___449_12532.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___449_12532.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___449_12532.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___449_12532.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12535 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12535 with
                | (f3,decls) ->
                    let g =
                      let uu____12549 =
                        let uu____12550 =
                          let uu____12558 =
                            let uu____12559 =
                              let uu____12561 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12561
                               in
                            FStar_Pervasives_Native.Some uu____12559  in
                          let uu____12565 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12558, uu____12565)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12550  in
                      [uu____12549]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12570) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12584 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12606 =
                       let uu____12609 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12609.FStar_Syntax_Syntax.fv_name  in
                     uu____12606.FStar_Syntax_Syntax.v  in
                   let uu____12610 =
                     let uu____12612 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12612  in
                   if uu____12610
                   then
                     let val_decl =
                       let uu___450_12644 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___450_12644.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___450_12644.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___450_12644.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12645 = encode_sigelt' env1 val_decl  in
                     match uu____12645 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12584 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12681,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12683;
                          FStar_Syntax_Syntax.lbtyp = uu____12684;
                          FStar_Syntax_Syntax.lbeff = uu____12685;
                          FStar_Syntax_Syntax.lbdef = uu____12686;
                          FStar_Syntax_Syntax.lbattrs = uu____12687;
                          FStar_Syntax_Syntax.lbpos = uu____12688;_}::[]),uu____12689)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12708 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12708 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12751 =
                   let uu____12754 =
                     let uu____12755 =
                       let uu____12763 =
                         let uu____12764 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12765 =
                           let uu____12776 =
                             let uu____12777 =
                               let uu____12782 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12782)  in
                             FStar_SMTEncoding_Util.mkEq uu____12777  in
                           ([[b2t_x]], [xx], uu____12776)  in
                         FStar_SMTEncoding_Term.mkForall uu____12764
                           uu____12765
                          in
                       (uu____12763,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12755  in
                   [uu____12754]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12751
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____12814,uu____12815) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___432_12825  ->
                  match uu___432_12825 with
                  | FStar_Syntax_Syntax.Discriminator uu____12827 -> true
                  | uu____12829 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____12831,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____12843 =
                     let uu____12845 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____12845.FStar_Ident.idText  in
                   uu____12843 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___433_12852  ->
                     match uu___433_12852 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12855 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12858) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___434_12872  ->
                  match uu___434_12872 with
                  | FStar_Syntax_Syntax.Projector uu____12874 -> true
                  | uu____12880 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12884 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12884 with
           | FStar_Pervasives_Native.Some uu____12891 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___451_12893 = se  in
                 let uu____12894 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12894;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___451_12893.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___451_12893.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___451_12893.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12897) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12912) ->
          let uu____12921 = encode_sigelts env ses  in
          (match uu____12921 with
           | (g,env1) ->
               let uu____12938 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___435_12961  ->
                         match uu___435_12961 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12963;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12964;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12965;_}
                             -> false
                         | uu____12972 -> true))
                  in
               (match uu____12938 with
                | (g',inversions) ->
                    let uu____12988 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___436_13009  ->
                              match uu___436_13009 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13011 ->
                                  true
                              | uu____13024 -> false))
                       in
                    (match uu____12988 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13041,tps,k,uu____13044,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___437_13063  ->
                    match uu___437_13063 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13067 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13080 = c  in
              match uu____13080 with
              | (name,args,uu____13085,uu____13086,uu____13087) ->
                  let uu____13098 =
                    let uu____13099 =
                      let uu____13111 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13138  ->
                                match uu____13138 with
                                | (uu____13147,sort,uu____13149) -> sort))
                         in
                      (name, uu____13111, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13099  in
                  [uu____13098]
            else
              (let uu____13160 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____13160 c)
             in
          let inversion_axioms tapp vars =
            let uu____13188 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13196 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____13196 FStar_Option.isNone))
               in
            if uu____13188
            then []
            else
              (let uu____13231 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____13231 with
               | (xxsym,xx) ->
                   let uu____13244 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13283  ->
                             fun l  ->
                               match uu____13283 with
                               | (out,decls) ->
                                   let uu____13303 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____13303 with
                                    | (uu____13314,data_t) ->
                                        let uu____13316 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13316 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13360 =
                                                 let uu____13361 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13361.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13360 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13364,indices) ->
                                                   indices
                                               | uu____13390 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13420  ->
                                                         match uu____13420
                                                         with
                                                         | (x,uu____13428) ->
                                                             let uu____13433
                                                               =
                                                               let uu____13434
                                                                 =
                                                                 let uu____13442
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13442,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13434
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13433)
                                                    env)
                                                in
                                             let uu____13447 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13447 with
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
                                                      let uu____13477 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13495
                                                                 =
                                                                 let uu____13500
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13500,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13495)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13477
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13503 =
                                                      let uu____13504 =
                                                        let uu____13509 =
                                                          let uu____13510 =
                                                            let uu____13515 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13515,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13510
                                                           in
                                                        (out, uu____13509)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13504
                                                       in
                                                    (uu____13503,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13244 with
                    | (data_ax,decls) ->
                        let uu____13528 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13528 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13545 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13545 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13552 =
                                 let uu____13560 =
                                   let uu____13561 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13562 =
                                     let uu____13573 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13586 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13573,
                                       uu____13586)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13561 uu____13562
                                    in
                                 let uu____13595 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13560,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13595)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13552
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13601 =
            let uu____13606 =
              let uu____13607 = FStar_Syntax_Subst.compress k  in
              uu____13607.FStar_Syntax_Syntax.n  in
            match uu____13606 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13642 -> (tps, k)  in
          (match uu____13601 with
           | (formals,res) ->
               let uu____13649 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13649 with
                | (formals1,res1) ->
                    let uu____13660 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13660 with
                     | (vars,guards,env',binder_decls,uu____13685) ->
                         let arity = FStar_List.length vars  in
                         let uu____13699 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13699 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13729 =
                                  let uu____13737 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13737)  in
                                FStar_SMTEncoding_Util.mkApp uu____13729  in
                              let uu____13743 =
                                let tname_decl =
                                  let uu____13753 =
                                    let uu____13754 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13782  ->
                                              match uu____13782 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13803 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13754,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13803, false)
                                     in
                                  constructor_or_logic_type_decl uu____13753
                                   in
                                let uu____13811 =
                                  match vars with
                                  | [] ->
                                      let uu____13824 =
                                        let uu____13825 =
                                          let uu____13828 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____13828
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____13825
                                         in
                                      ([], uu____13824)
                                  | uu____13840 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13850 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13850
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13866 =
                                          let uu____13874 =
                                            let uu____13875 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13876 =
                                              let uu____13892 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13892)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13875 uu____13876
                                             in
                                          (uu____13874,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13866
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13811 with
                                | (tok_decls,env2) ->
                                    let uu____13919 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13919
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13743 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13947 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13947 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13969 =
                                               let uu____13970 =
                                                 let uu____13978 =
                                                   let uu____13979 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13979
                                                    in
                                                 (uu____13978,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13970
                                                in
                                             [uu____13969]
                                           else []  in
                                         let uu____13987 =
                                           let uu____13990 =
                                             let uu____13993 =
                                               let uu____13994 =
                                                 let uu____14002 =
                                                   let uu____14003 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____14004 =
                                                     let uu____14015 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14015)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____14003 uu____14004
                                                    in
                                                 (uu____14002,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13994
                                                in
                                             [uu____13993]  in
                                           FStar_List.append karr uu____13990
                                            in
                                         FStar_List.append decls1 uu____13987
                                      in
                                   let aux =
                                     let uu____14030 =
                                       let uu____14033 =
                                         inversion_axioms tapp vars  in
                                       let uu____14036 =
                                         let uu____14039 =
                                           let uu____14040 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____14040 env2
                                             tapp vars
                                            in
                                         [uu____14039]  in
                                       FStar_List.append uu____14033
                                         uu____14036
                                        in
                                     FStar_List.append kindingAx uu____14030
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14045,uu____14046,uu____14047,uu____14048,uu____14049)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14057,t,uu____14059,n_tps,uu____14061) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____14071 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____14071 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____14119 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____14119 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____14147 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____14147 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14167 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____14167 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14246 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____14246,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14253 =
                                  let uu____14254 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14254, true)
                                   in
                                let uu____14262 =
                                  let uu____14269 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____14269
                                   in
                                FStar_All.pipe_right uu____14253 uu____14262
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
                              let uu____14281 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____14281 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14293::uu____14294 ->
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
                                         let uu____14353 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____14354 =
                                           let uu____14365 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14365)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____14353 uu____14354
                                     | uu____14386 -> tok_typing  in
                                   let uu____14397 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14397 with
                                    | (vars',guards',env'',decls_formals,uu____14422)
                                        ->
                                        let uu____14435 =
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
                                        (match uu____14435 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14465 ->
                                                   let uu____14474 =
                                                     let uu____14475 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14475
                                                      in
                                                   [uu____14474]
                                                in
                                             let encode_elim uu____14491 =
                                               let uu____14492 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14492 with
                                               | (head1,args) ->
                                                   let uu____14543 =
                                                     let uu____14544 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14544.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14543 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14556;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14557;_},uu____14558)
                                                        ->
                                                        let uu____14563 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14563
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14584
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14584
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
                                                                    uu____14638
                                                                    ->
                                                                    let uu____14639
                                                                    =
                                                                    let uu____14645
                                                                    =
                                                                    let uu____14647
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14647
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14645)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14639
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14669
                                                                     in
                                                                    if
                                                                    uu____14667
                                                                    then
                                                                    let uu____14685
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14685]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14688
                                                                    =
                                                                    let uu____14702
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14759
                                                                     ->
                                                                    fun
                                                                    uu____14760
                                                                     ->
                                                                    match 
                                                                    (uu____14759,
                                                                    uu____14760)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14879
                                                                     in
                                                                    (match uu____14871
                                                                    with
                                                                    | 
                                                                    (uu____14893,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14904
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14904
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14909
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14909
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
                                                                    uu____14702
                                                                     in
                                                                  (match uu____14688
                                                                   with
                                                                   | 
                                                                   (uu____14930,arg_vars,elim_eqns_or_guards,uu____14933)
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
                                                                    let uu____14960
                                                                    =
                                                                    let uu____14968
                                                                    =
                                                                    let uu____14969
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14981
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14983
                                                                    =
                                                                    let uu____14984
                                                                    =
                                                                    let uu____14989
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14989)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14984
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14981,
                                                                    uu____14983)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14969
                                                                    uu____14970
                                                                     in
                                                                    (uu____14968,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14960
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15004
                                                                    =
                                                                    let uu____15010
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15010,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15004
                                                                     in
                                                                    let uu____15013
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15013
                                                                    then
                                                                    let x =
                                                                    let uu____15022
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15022,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15027
                                                                    =
                                                                    let uu____15035
                                                                    =
                                                                    let uu____15036
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15037
                                                                    =
                                                                    let uu____15048
                                                                    =
                                                                    let uu____15053
                                                                    =
                                                                    let uu____15056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15056]
                                                                     in
                                                                    [uu____15053]
                                                                     in
                                                                    let uu____15061
                                                                    =
                                                                    let uu____15062
                                                                    =
                                                                    let uu____15067
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15069
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15067,
                                                                    uu____15069)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15062
                                                                     in
                                                                    (uu____15048,
                                                                    [x],
                                                                    uu____15061)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15036
                                                                    uu____15037
                                                                     in
                                                                    let uu____15084
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15035,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15084)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15027
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15095
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
                                                                    (let uu____15133
                                                                    =
                                                                    let uu____15134
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15134
                                                                    dapp1  in
                                                                    [uu____15133])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15095
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15141
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    let uu____15150
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15151
                                                                    =
                                                                    let uu____15162
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15164
                                                                    =
                                                                    let uu____15165
                                                                    =
                                                                    let uu____15170
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15170)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15165
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15162,
                                                                    uu____15164)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15150
                                                                    uu____15151
                                                                     in
                                                                    (uu____15149,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15141)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____15188 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____15188
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____15209
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____15209
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
                                                                    uu____15263
                                                                    ->
                                                                    let uu____15264
                                                                    =
                                                                    let uu____15270
                                                                    =
                                                                    let uu____15272
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15272
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15270)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15264
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15292
                                                                    =
                                                                    let uu____15294
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15294
                                                                     in
                                                                    if
                                                                    uu____15292
                                                                    then
                                                                    let uu____15310
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15310]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____15313
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15384
                                                                     ->
                                                                    fun
                                                                    uu____15385
                                                                     ->
                                                                    match 
                                                                    (uu____15384,
                                                                    uu____15385)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15496
                                                                    =
                                                                    let uu____15504
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15504
                                                                     in
                                                                    (match uu____15496
                                                                    with
                                                                    | 
                                                                    (uu____15518,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15529
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15529
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15534
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15534
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
                                                                    uu____15327
                                                                     in
                                                                  (match uu____15313
                                                                   with
                                                                   | 
                                                                   (uu____15555,arg_vars,elim_eqns_or_guards,uu____15558)
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
                                                                    let uu____15585
                                                                    =
                                                                    let uu____15593
                                                                    =
                                                                    let uu____15594
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15595
                                                                    =
                                                                    let uu____15606
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15608
                                                                    =
                                                                    let uu____15609
                                                                    =
                                                                    let uu____15614
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15614)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15609
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15606,
                                                                    uu____15608)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15594
                                                                    uu____15595
                                                                     in
                                                                    (uu____15593,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15585
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15629
                                                                    =
                                                                    let uu____15635
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15635,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15629
                                                                     in
                                                                    let uu____15638
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15638
                                                                    then
                                                                    let x =
                                                                    let uu____15647
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15647,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15652
                                                                    =
                                                                    let uu____15660
                                                                    =
                                                                    let uu____15661
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15662
                                                                    =
                                                                    let uu____15673
                                                                    =
                                                                    let uu____15678
                                                                    =
                                                                    let uu____15681
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15681]
                                                                     in
                                                                    [uu____15678]
                                                                     in
                                                                    let uu____15686
                                                                    =
                                                                    let uu____15687
                                                                    =
                                                                    let uu____15692
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15694
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15692,
                                                                    uu____15694)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15687
                                                                     in
                                                                    (uu____15673,
                                                                    [x],
                                                                    uu____15686)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15661
                                                                    uu____15662
                                                                     in
                                                                    let uu____15709
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15660,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15709)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15652
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15720
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
                                                                    (let uu____15758
                                                                    =
                                                                    let uu____15759
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15759
                                                                    dapp1  in
                                                                    [uu____15758])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15720
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15766
                                                                    =
                                                                    let uu____15774
                                                                    =
                                                                    let uu____15775
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15776
                                                                    =
                                                                    let uu____15787
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15789
                                                                    =
                                                                    let uu____15790
                                                                    =
                                                                    let uu____15795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15795)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15790
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15787,
                                                                    uu____15789)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15775
                                                                    uu____15776
                                                                     in
                                                                    (uu____15774,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15766)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15812 ->
                                                        ((let uu____15814 =
                                                            let uu____15820 =
                                                              let uu____15822
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____15824
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____15822
                                                                uu____15824
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____15820)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15814);
                                                         ([], [])))
                                                in
                                             let uu____15832 = encode_elim ()
                                                in
                                             (match uu____15832 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15858 =
                                                      let uu____15861 =
                                                        let uu____15864 =
                                                          let uu____15867 =
                                                            let uu____15870 =
                                                              let uu____15871
                                                                =
                                                                let uu____15883
                                                                  =
                                                                  let uu____15884
                                                                    =
                                                                    let uu____15886
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15886
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15884
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15883)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15871
                                                               in
                                                            [uu____15870]  in
                                                          let uu____15893 =
                                                            let uu____15896 =
                                                              let uu____15899
                                                                =
                                                                let uu____15902
                                                                  =
                                                                  let uu____15905
                                                                    =
                                                                    let uu____15908
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15913
                                                                    =
                                                                    let uu____15916
                                                                    =
                                                                    let uu____15917
                                                                    =
                                                                    let uu____15925
                                                                    =
                                                                    let uu____15926
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15927
                                                                    =
                                                                    let uu____15938
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15938)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15926
                                                                    uu____15927
                                                                     in
                                                                    (uu____15925,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15917
                                                                     in
                                                                    let uu____15951
                                                                    =
                                                                    let uu____15954
                                                                    =
                                                                    let uu____15955
                                                                    =
                                                                    let uu____15963
                                                                    =
                                                                    let uu____15964
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15965
                                                                    =
                                                                    let uu____15976
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15976,
                                                                    uu____15978)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15964
                                                                    uu____15965
                                                                     in
                                                                    (uu____15963,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15955
                                                                     in
                                                                    [uu____15954]
                                                                     in
                                                                    uu____15916
                                                                    ::
                                                                    uu____15951
                                                                     in
                                                                    uu____15908
                                                                    ::
                                                                    uu____15913
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15905
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15902
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15899
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15896
                                                             in
                                                          FStar_List.append
                                                            uu____15867
                                                            uu____15893
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15864
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15861
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15858
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
           (fun uu____16016  ->
              fun se  ->
                match uu____16016 with
                | (g,env1) ->
                    let uu____16036 = encode_sigelt env1 se  in
                    (match uu____16036 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16104 =
        match uu____16104 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____16141 ->
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
                 ((let uu____16149 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____16149
                   then
                     let uu____16154 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____16156 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____16158 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16154 uu____16156 uu____16158
                   else ());
                  (let uu____16163 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____16163 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____16181 =
                         let uu____16189 =
                           let uu____16191 =
                             let uu____16193 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16193
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16191  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16189
                          in
                       (match uu____16181 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16213 = FStar_Options.log_queries ()
                                 in
                              if uu____16213
                              then
                                let uu____16216 =
                                  let uu____16218 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16220 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16222 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16218 uu____16220 uu____16222
                                   in
                                FStar_Pervasives_Native.Some uu____16216
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16246,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16266 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16266 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16293 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16293 with | (uu____16320,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____16336 'Auu____16337 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____16336 *
      'Auu____16337) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16410  ->
              match uu____16410 with
              | (l,uu____16423,uu____16424) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16475  ->
              match uu____16475 with
              | (l,uu____16490,uu____16491) ->
                  let uu____16502 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16505 =
                    let uu____16508 =
                      let uu____16509 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16509  in
                    [uu____16508]  in
                  uu____16502 :: uu____16505))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16538 =
      let uu____16541 =
        let uu____16542 = FStar_Util.psmap_empty ()  in
        let uu____16557 = FStar_Util.psmap_empty ()  in
        let uu____16560 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16564 =
          let uu____16566 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16566 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16542;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16557;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16560;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16564;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16541]  in
    FStar_ST.op_Colon_Equals last_env uu____16538
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16608 = FStar_ST.op_Bang last_env  in
      match uu____16608 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16636 ->
          let uu___452_16639 = e  in
          let uu____16640 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___452_16639.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___452_16639.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___452_16639.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___452_16639.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___452_16639.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___452_16639.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___452_16639.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___452_16639.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16640;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___452_16639.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16648 = FStar_ST.op_Bang last_env  in
    match uu____16648 with
    | [] -> failwith "Empty env stack"
    | uu____16675::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16707  ->
    let uu____16708 = FStar_ST.op_Bang last_env  in
    match uu____16708 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16768  ->
    let uu____16769 = FStar_ST.op_Bang last_env  in
    match uu____16769 with
    | [] -> failwith "Popping an empty stack"
    | uu____16796::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16833  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16886  ->
         let uu____16887 = snapshot_env ()  in
         match uu____16887 with
         | (env_depth,()) ->
             let uu____16909 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16909 with
              | (varops_depth,()) ->
                  let uu____16931 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16931 with
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
        (fun uu____16989  ->
           let uu____16990 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16990 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____17085 = snapshot msg  in () 
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
        | (uu____17131::uu____17132,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___453_17140 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___453_17140.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___453_17140.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___453_17140.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17141 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____17161 =
        let uu____17164 =
          let uu____17165 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____17165  in
        let uu____17166 = open_fact_db_tags env  in uu____17164 ::
          uu____17166
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17161
  
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
      let uu____17193 = encode_sigelt env se  in
      match uu____17193 with
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
        let uu____17238 = FStar_Options.log_queries ()  in
        if uu____17238
        then
          let uu____17243 =
            let uu____17244 =
              let uu____17246 =
                let uu____17248 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17248 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17246  in
            FStar_SMTEncoding_Term.Caption uu____17244  in
          uu____17243 :: decls
        else decls  in
      (let uu____17267 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____17267
       then
         let uu____17270 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17270
       else ());
      (let env =
         let uu____17276 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17276 tcenv  in
       let uu____17277 = encode_top_level_facts env se  in
       match uu____17277 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17291 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17291)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17305 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17305
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17320 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____17320
          then
            let uu____17323 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17323
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17369  ->
                    fun se  ->
                      match uu____17369 with
                      | (g,env2) ->
                          let uu____17389 = encode_top_level_facts env2 se
                             in
                          (match uu____17389 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17412 =
            encode_signature
              (let uu___454_17421 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___454_17421.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___454_17421.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___454_17421.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___454_17421.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___454_17421.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___454_17421.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___454_17421.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___454_17421.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___454_17421.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___454_17421.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17412 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17441 = FStar_Options.log_queries ()  in
                if uu____17441
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
                 (let uu___455_17458 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___455_17458.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___455_17458.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___455_17458.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___455_17458.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___455_17458.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___455_17458.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___455_17458.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___455_17458.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___455_17458.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___455_17458.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17461 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17461
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
        (let uu____17526 =
           let uu____17528 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17528.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17526);
        (let env =
           let uu____17530 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17530 tcenv  in
         let uu____17531 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17570 = aux rest  in
                 (match uu____17570 with
                  | (out,rest1) ->
                      let t =
                        let uu____17598 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17598 with
                        | FStar_Pervasives_Native.Some uu____17601 ->
                            let uu____17602 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17602
                              x.FStar_Syntax_Syntax.sort
                        | uu____17603 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17607 =
                        let uu____17610 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___456_17613 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___456_17613.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___456_17613.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17610 :: out  in
                      (uu____17607, rest1))
             | uu____17618 -> ([], bindings)  in
           let uu____17625 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17625 with
           | (closing,bindings) ->
               let uu____17652 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17652, bindings)
            in
         match uu____17531 with
         | (q1,bindings) ->
             let uu____17683 = encode_env_bindings env bindings  in
             (match uu____17683 with
              | (env_decls,env1) ->
                  ((let uu____17705 =
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
                    if uu____17705
                    then
                      let uu____17712 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17712
                    else ());
                   (let uu____17717 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17717 with
                    | (phi,qdecls) ->
                        let uu____17738 =
                          let uu____17743 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17743 phi
                           in
                        (match uu____17738 with
                         | (labels,phi1) ->
                             let uu____17760 = encode_labels labels  in
                             (match uu____17760 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17797 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17797
                                    then
                                      let uu____17802 =
                                        let uu____17803 =
                                          let uu____17805 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17805
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17803
                                         in
                                      [uu____17802]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17814 =
                                      let uu____17822 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17823 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17822,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17823)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17814
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
  