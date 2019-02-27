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
  let module_name = "Prims"  in
  let uu____72779 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72779 with
  | (asym,a) ->
      let uu____72790 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72790 with
       | (xsym,x) ->
           let uu____72801 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72801 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72879 =
                      let uu____72891 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72891, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72879  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72911 =
                      let uu____72919 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72919)  in
                    FStar_SMTEncoding_Util.mkApp uu____72911  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____72938 =
                    let uu____72941 =
                      let uu____72944 =
                        let uu____72947 =
                          let uu____72948 =
                            let uu____72956 =
                              let uu____72957 =
                                let uu____72968 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____72968)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____72957
                               in
                            (uu____72956, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____72948  in
                        let uu____72980 =
                          let uu____72983 =
                            let uu____72984 =
                              let uu____72992 =
                                let uu____72993 =
                                  let uu____73004 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____73004)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____72993
                                 in
                              (uu____72992,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____72984  in
                          [uu____72983]  in
                        uu____72947 :: uu____72980  in
                      xtok_decl :: uu____72944  in
                    xname_decl :: uu____72941  in
                  (xtok1, (FStar_List.length vars), uu____72938)  in
                let axy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(asym, FStar_SMTEncoding_Term.Term_sort);
                    (xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let xy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let qx =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort)]
                   in
                let prims1 =
                  let uu____73174 =
                    let uu____73195 =
                      let uu____73214 =
                        let uu____73215 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73215
                         in
                      quant axy uu____73214  in
                    (FStar_Parser_Const.op_Eq, uu____73195)  in
                  let uu____73232 =
                    let uu____73255 =
                      let uu____73276 =
                        let uu____73295 =
                          let uu____73296 =
                            let uu____73297 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73297  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73296
                           in
                        quant axy uu____73295  in
                      (FStar_Parser_Const.op_notEq, uu____73276)  in
                    let uu____73314 =
                      let uu____73337 =
                        let uu____73358 =
                          let uu____73377 =
                            let uu____73378 =
                              let uu____73379 =
                                let uu____73384 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73385 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73384, uu____73385)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73379  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73378
                             in
                          quant xy uu____73377  in
                        (FStar_Parser_Const.op_And, uu____73358)  in
                      let uu____73402 =
                        let uu____73425 =
                          let uu____73446 =
                            let uu____73465 =
                              let uu____73466 =
                                let uu____73467 =
                                  let uu____73472 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73473 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73472, uu____73473)  in
                                FStar_SMTEncoding_Util.mkOr uu____73467  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73466
                               in
                            quant xy uu____73465  in
                          (FStar_Parser_Const.op_Or, uu____73446)  in
                        let uu____73490 =
                          let uu____73513 =
                            let uu____73534 =
                              let uu____73553 =
                                let uu____73554 =
                                  let uu____73555 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73555
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73554
                                 in
                              quant qx uu____73553  in
                            (FStar_Parser_Const.op_Negation, uu____73534)  in
                          let uu____73572 =
                            let uu____73595 =
                              let uu____73616 =
                                let uu____73635 =
                                  let uu____73636 =
                                    let uu____73637 =
                                      let uu____73642 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73643 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73642, uu____73643)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73637
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73636
                                   in
                                quant xy uu____73635  in
                              (FStar_Parser_Const.op_LT, uu____73616)  in
                            let uu____73660 =
                              let uu____73683 =
                                let uu____73704 =
                                  let uu____73723 =
                                    let uu____73724 =
                                      let uu____73725 =
                                        let uu____73730 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73731 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73730, uu____73731)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73725
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73724
                                     in
                                  quant xy uu____73723  in
                                (FStar_Parser_Const.op_LTE, uu____73704)  in
                              let uu____73748 =
                                let uu____73771 =
                                  let uu____73792 =
                                    let uu____73811 =
                                      let uu____73812 =
                                        let uu____73813 =
                                          let uu____73818 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73819 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73818, uu____73819)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73813
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73812
                                       in
                                    quant xy uu____73811  in
                                  (FStar_Parser_Const.op_GT, uu____73792)  in
                                let uu____73836 =
                                  let uu____73859 =
                                    let uu____73880 =
                                      let uu____73899 =
                                        let uu____73900 =
                                          let uu____73901 =
                                            let uu____73906 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73907 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73906, uu____73907)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73901
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73900
                                         in
                                      quant xy uu____73899  in
                                    (FStar_Parser_Const.op_GTE, uu____73880)
                                     in
                                  let uu____73924 =
                                    let uu____73947 =
                                      let uu____73968 =
                                        let uu____73987 =
                                          let uu____73988 =
                                            let uu____73989 =
                                              let uu____73994 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____73995 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____73994, uu____73995)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____73989
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____73988
                                           in
                                        quant xy uu____73987  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____73968)
                                       in
                                    let uu____74012 =
                                      let uu____74035 =
                                        let uu____74056 =
                                          let uu____74075 =
                                            let uu____74076 =
                                              let uu____74077 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74077
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74076
                                             in
                                          quant qx uu____74075  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74056)
                                         in
                                      let uu____74094 =
                                        let uu____74117 =
                                          let uu____74138 =
                                            let uu____74157 =
                                              let uu____74158 =
                                                let uu____74159 =
                                                  let uu____74164 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74165 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74164, uu____74165)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74159
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74158
                                               in
                                            quant xy uu____74157  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74138)
                                           in
                                        let uu____74182 =
                                          let uu____74205 =
                                            let uu____74226 =
                                              let uu____74245 =
                                                let uu____74246 =
                                                  let uu____74247 =
                                                    let uu____74252 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74253 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74252,
                                                      uu____74253)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74247
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74246
                                                 in
                                              quant xy uu____74245  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74226)
                                             in
                                          let uu____74270 =
                                            let uu____74293 =
                                              let uu____74314 =
                                                let uu____74333 =
                                                  let uu____74334 =
                                                    let uu____74335 =
                                                      let uu____74340 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74341 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74340,
                                                        uu____74341)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74335
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74334
                                                   in
                                                quant xy uu____74333  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74314)
                                               in
                                            let uu____74358 =
                                              let uu____74381 =
                                                let uu____74402 =
                                                  let uu____74421 =
                                                    let uu____74422 =
                                                      let uu____74423 =
                                                        let uu____74428 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74429 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74428,
                                                          uu____74429)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74423
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74422
                                                     in
                                                  quant xy uu____74421  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74402)
                                                 in
                                              let uu____74446 =
                                                let uu____74469 =
                                                  let uu____74490 =
                                                    let uu____74509 =
                                                      let uu____74510 =
                                                        let uu____74511 =
                                                          let uu____74516 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74517 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74516,
                                                            uu____74517)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74511
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74510
                                                       in
                                                    quant xy uu____74509  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74490)
                                                   in
                                                let uu____74534 =
                                                  let uu____74557 =
                                                    let uu____74578 =
                                                      let uu____74597 =
                                                        let uu____74598 =
                                                          let uu____74599 =
                                                            let uu____74604 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74605 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74604,
                                                              uu____74605)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74599
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74598
                                                         in
                                                      quant xy uu____74597
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74578)
                                                     in
                                                  let uu____74622 =
                                                    let uu____74645 =
                                                      let uu____74666 =
                                                        let uu____74685 =
                                                          let uu____74686 =
                                                            let uu____74687 =
                                                              let uu____74692
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74693
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74692,
                                                                uu____74693)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74687
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74686
                                                           in
                                                        quant xy uu____74685
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74666)
                                                       in
                                                    let uu____74710 =
                                                      let uu____74733 =
                                                        let uu____74754 =
                                                          let uu____74773 =
                                                            let uu____74774 =
                                                              let uu____74775
                                                                =
                                                                let uu____74780
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74781
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74780,
                                                                  uu____74781)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74775
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74774
                                                             in
                                                          quant xy
                                                            uu____74773
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74754)
                                                         in
                                                      let uu____74798 =
                                                        let uu____74821 =
                                                          let uu____74842 =
                                                            let uu____74861 =
                                                              let uu____74862
                                                                =
                                                                let uu____74863
                                                                  =
                                                                  let uu____74868
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74869
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74868,
                                                                    uu____74869)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74863
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74862
                                                               in
                                                            quant xy
                                                              uu____74861
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74842)
                                                           in
                                                        let uu____74886 =
                                                          let uu____74909 =
                                                            let uu____74930 =
                                                              let uu____74949
                                                                =
                                                                let uu____74950
                                                                  =
                                                                  let uu____74951
                                                                    =
                                                                    let uu____74956
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74957
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74956,
                                                                    uu____74957)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____74951
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____74950
                                                                 in
                                                              quant xy
                                                                uu____74949
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74930)
                                                             in
                                                          let uu____74974 =
                                                            let uu____74997 =
                                                              let uu____75018
                                                                =
                                                                let uu____75037
                                                                  =
                                                                  let uu____75038
                                                                    =
                                                                    let uu____75039
                                                                    =
                                                                    let uu____75044
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75045
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75044,
                                                                    uu____75045)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75039
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75038
                                                                   in
                                                                quant xy
                                                                  uu____75037
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75018)
                                                               in
                                                            let uu____75062 =
                                                              let uu____75085
                                                                =
                                                                let uu____75106
                                                                  =
                                                                  let uu____75125
                                                                    =
                                                                    let uu____75126
                                                                    =
                                                                    let uu____75127
                                                                    =
                                                                    let uu____75132
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75133
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75132,
                                                                    uu____75133)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75127
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75126
                                                                     in
                                                                  quant xy
                                                                    uu____75125
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75106)
                                                                 in
                                                              let uu____75150
                                                                =
                                                                let uu____75173
                                                                  =
                                                                  let uu____75194
                                                                    =
                                                                    let uu____75213
                                                                    =
                                                                    let uu____75214
                                                                    =
                                                                    let uu____75215
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75215
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75214
                                                                     in
                                                                    quant qx
                                                                    uu____75213
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75194)
                                                                   in
                                                                [uu____75173]
                                                                 in
                                                              uu____75085 ::
                                                                uu____75150
                                                               in
                                                            uu____74997 ::
                                                              uu____75062
                                                             in
                                                          uu____74909 ::
                                                            uu____74974
                                                           in
                                                        uu____74821 ::
                                                          uu____74886
                                                         in
                                                      uu____74733 ::
                                                        uu____74798
                                                       in
                                                    uu____74645 ::
                                                      uu____74710
                                                     in
                                                  uu____74557 :: uu____74622
                                                   in
                                                uu____74469 :: uu____74534
                                                 in
                                              uu____74381 :: uu____74446  in
                                            uu____74293 :: uu____74358  in
                                          uu____74205 :: uu____74270  in
                                        uu____74117 :: uu____74182  in
                                      uu____74035 :: uu____74094  in
                                    uu____73947 :: uu____74012  in
                                  uu____73859 :: uu____73924  in
                                uu____73771 :: uu____73836  in
                              uu____73683 :: uu____73748  in
                            uu____73595 :: uu____73660  in
                          uu____73513 :: uu____73572  in
                        uu____73425 :: uu____73490  in
                      uu____73337 :: uu____73402  in
                    uu____73255 :: uu____73314  in
                  uu____73174 :: uu____73232  in
                let mk1 l v1 =
                  let uu____75754 =
                    let uu____75766 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75856  ->
                              match uu____75856 with
                              | (l',uu____75877) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75766
                      (FStar_Option.map
                         (fun uu____75976  ->
                            match uu____75976 with
                            | (uu____76004,b) ->
                                let uu____76038 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76038 v1))
                     in
                  FStar_All.pipe_right uu____75754 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76121  ->
                          match uu____76121 with
                          | (l',uu____76142) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list
          -> FStar_SMTEncoding_Term.decl)
  =
  fun rng  ->
    fun env  ->
      fun tapp  ->
        fun vars  ->
          let uu____76216 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76216 with
          | (xxsym,xx) ->
              let uu____76227 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76227 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76243 =
                     let uu____76251 =
                       let uu____76252 =
                         let uu____76263 =
                           let uu____76264 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76274 =
                             let uu____76285 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76285 :: vars  in
                           uu____76264 :: uu____76274  in
                         let uu____76311 =
                           let uu____76312 =
                             let uu____76317 =
                               let uu____76318 =
                                 let uu____76323 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76323)  in
                               FStar_SMTEncoding_Util.mkEq uu____76318  in
                             (xx_has_type, uu____76317)  in
                           FStar_SMTEncoding_Util.mkImp uu____76312  in
                         ([[xx_has_type]], uu____76263, uu____76311)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76252  in
                     let uu____76336 =
                       let uu____76338 =
                         let uu____76340 =
                           let uu____76342 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76342  in
                         Prims.op_Hat module_name uu____76340  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76338
                        in
                     (uu____76251,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76336)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76243)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx =
    FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy =
    FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mkForall_fuel1 env =
    let uu____76398 =
      let uu____76400 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76400  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76398  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76422 =
      let uu____76423 =
        let uu____76431 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76431, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76423  in
    let uu____76436 =
      let uu____76439 =
        let uu____76440 =
          let uu____76448 =
            let uu____76449 =
              let uu____76460 =
                let uu____76461 =
                  let uu____76466 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76466)  in
                FStar_SMTEncoding_Util.mkImp uu____76461  in
              ([[typing_pred]], [xx], uu____76460)  in
            let uu____76491 =
              let uu____76506 = FStar_TypeChecker_Env.get_range env  in
              let uu____76507 = mkForall_fuel1 env  in
              uu____76507 uu____76506  in
            uu____76491 uu____76449  in
          (uu____76448, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76440  in
      [uu____76439]  in
    uu____76422 :: uu____76436  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76554 =
      let uu____76555 =
        let uu____76563 =
          let uu____76564 = FStar_TypeChecker_Env.get_range env  in
          let uu____76565 =
            let uu____76576 =
              let uu____76581 =
                let uu____76584 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76584]  in
              [uu____76581]  in
            let uu____76589 =
              let uu____76590 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76590 tt  in
            (uu____76576, [bb], uu____76589)  in
          FStar_SMTEncoding_Term.mkForall uu____76564 uu____76565  in
        (uu____76563, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76555  in
    let uu____76615 =
      let uu____76618 =
        let uu____76619 =
          let uu____76627 =
            let uu____76628 =
              let uu____76639 =
                let uu____76640 =
                  let uu____76645 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76645)  in
                FStar_SMTEncoding_Util.mkImp uu____76640  in
              ([[typing_pred]], [xx], uu____76639)  in
            let uu____76672 =
              let uu____76687 = FStar_TypeChecker_Env.get_range env  in
              let uu____76688 = mkForall_fuel1 env  in
              uu____76688 uu____76687  in
            uu____76672 uu____76628  in
          (uu____76627, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76619  in
      [uu____76618]  in
    uu____76554 :: uu____76615  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76731 =
        let uu____76732 =
          let uu____76738 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76738, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76732  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76731  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76752 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76752  in
    let uu____76757 =
      let uu____76758 =
        let uu____76766 =
          let uu____76767 = FStar_TypeChecker_Env.get_range env  in
          let uu____76768 =
            let uu____76779 =
              let uu____76784 =
                let uu____76787 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76787]  in
              [uu____76784]  in
            let uu____76792 =
              let uu____76793 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76793 tt  in
            (uu____76779, [bb], uu____76792)  in
          FStar_SMTEncoding_Term.mkForall uu____76767 uu____76768  in
        (uu____76766, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76758  in
    let uu____76818 =
      let uu____76821 =
        let uu____76822 =
          let uu____76830 =
            let uu____76831 =
              let uu____76842 =
                let uu____76843 =
                  let uu____76848 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76848)  in
                FStar_SMTEncoding_Util.mkImp uu____76843  in
              ([[typing_pred]], [xx], uu____76842)  in
            let uu____76875 =
              let uu____76890 = FStar_TypeChecker_Env.get_range env  in
              let uu____76891 = mkForall_fuel1 env  in
              uu____76891 uu____76890  in
            uu____76875 uu____76831  in
          (uu____76830, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76822  in
      let uu____76913 =
        let uu____76916 =
          let uu____76917 =
            let uu____76925 =
              let uu____76926 =
                let uu____76937 =
                  let uu____76938 =
                    let uu____76943 =
                      let uu____76944 =
                        let uu____76947 =
                          let uu____76950 =
                            let uu____76953 =
                              let uu____76954 =
                                let uu____76959 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____76960 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____76959, uu____76960)  in
                              FStar_SMTEncoding_Util.mkGT uu____76954  in
                            let uu____76962 =
                              let uu____76965 =
                                let uu____76966 =
                                  let uu____76971 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____76972 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____76971, uu____76972)  in
                                FStar_SMTEncoding_Util.mkGTE uu____76966  in
                              let uu____76974 =
                                let uu____76977 =
                                  let uu____76978 =
                                    let uu____76983 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____76984 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____76983, uu____76984)  in
                                  FStar_SMTEncoding_Util.mkLT uu____76978  in
                                [uu____76977]  in
                              uu____76965 :: uu____76974  in
                            uu____76953 :: uu____76962  in
                          typing_pred_y :: uu____76950  in
                        typing_pred :: uu____76947  in
                      FStar_SMTEncoding_Util.mk_and_l uu____76944  in
                    (uu____76943, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____76938  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____76937)
                 in
              let uu____77017 =
                let uu____77032 = FStar_TypeChecker_Env.get_range env  in
                let uu____77033 = mkForall_fuel1 env  in
                uu____77033 uu____77032  in
              uu____77017 uu____76926  in
            (uu____76925,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76917  in
        [uu____76916]  in
      uu____76821 :: uu____76913  in
    uu____76757 :: uu____76818  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77076 =
        let uu____77077 =
          let uu____77083 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77083, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77077  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77076  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv
        ("a", (FStar_SMTEncoding_Term.Sort "Real"))
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv
        ("b", (FStar_SMTEncoding_Term.Sort "Real"))
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____77099 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77099  in
    let uu____77104 =
      let uu____77105 =
        let uu____77113 =
          let uu____77114 = FStar_TypeChecker_Env.get_range env  in
          let uu____77115 =
            let uu____77126 =
              let uu____77131 =
                let uu____77134 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77134]  in
              [uu____77131]  in
            let uu____77139 =
              let uu____77140 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77140 tt  in
            (uu____77126, [bb], uu____77139)  in
          FStar_SMTEncoding_Term.mkForall uu____77114 uu____77115  in
        (uu____77113, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77105  in
    let uu____77165 =
      let uu____77168 =
        let uu____77169 =
          let uu____77177 =
            let uu____77178 =
              let uu____77189 =
                let uu____77190 =
                  let uu____77195 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77195)  in
                FStar_SMTEncoding_Util.mkImp uu____77190  in
              ([[typing_pred]], [xx], uu____77189)  in
            let uu____77222 =
              let uu____77237 = FStar_TypeChecker_Env.get_range env  in
              let uu____77238 = mkForall_fuel1 env  in
              uu____77238 uu____77237  in
            uu____77222 uu____77178  in
          (uu____77177, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77169  in
      let uu____77260 =
        let uu____77263 =
          let uu____77264 =
            let uu____77272 =
              let uu____77273 =
                let uu____77284 =
                  let uu____77285 =
                    let uu____77290 =
                      let uu____77291 =
                        let uu____77294 =
                          let uu____77297 =
                            let uu____77300 =
                              let uu____77301 =
                                let uu____77306 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77307 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77306, uu____77307)  in
                              FStar_SMTEncoding_Util.mkGT uu____77301  in
                            let uu____77309 =
                              let uu____77312 =
                                let uu____77313 =
                                  let uu____77318 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77319 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77318, uu____77319)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77313  in
                              let uu____77321 =
                                let uu____77324 =
                                  let uu____77325 =
                                    let uu____77330 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77331 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77330, uu____77331)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77325  in
                                [uu____77324]  in
                              uu____77312 :: uu____77321  in
                            uu____77300 :: uu____77309  in
                          typing_pred_y :: uu____77297  in
                        typing_pred :: uu____77294  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77291  in
                    (uu____77290, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77285  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77284)
                 in
              let uu____77364 =
                let uu____77379 = FStar_TypeChecker_Env.get_range env  in
                let uu____77380 = mkForall_fuel1 env  in
                uu____77380 uu____77379  in
              uu____77364 uu____77273  in
            (uu____77272,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77264  in
        [uu____77263]  in
      uu____77168 :: uu____77260  in
    uu____77104 :: uu____77165  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77427 =
      let uu____77428 =
        let uu____77436 =
          let uu____77437 = FStar_TypeChecker_Env.get_range env  in
          let uu____77438 =
            let uu____77449 =
              let uu____77454 =
                let uu____77457 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77457]  in
              [uu____77454]  in
            let uu____77462 =
              let uu____77463 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77463 tt  in
            (uu____77449, [bb], uu____77462)  in
          FStar_SMTEncoding_Term.mkForall uu____77437 uu____77438  in
        (uu____77436, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77428  in
    let uu____77488 =
      let uu____77491 =
        let uu____77492 =
          let uu____77500 =
            let uu____77501 =
              let uu____77512 =
                let uu____77513 =
                  let uu____77518 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77518)  in
                FStar_SMTEncoding_Util.mkImp uu____77513  in
              ([[typing_pred]], [xx], uu____77512)  in
            let uu____77545 =
              let uu____77560 = FStar_TypeChecker_Env.get_range env  in
              let uu____77561 = mkForall_fuel1 env  in
              uu____77561 uu____77560  in
            uu____77545 uu____77501  in
          (uu____77500, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77492  in
      [uu____77491]  in
    uu____77427 :: uu____77488  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77608 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77608]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77638 =
      let uu____77639 =
        let uu____77647 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77647, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77639  in
    [uu____77638]  in
  let mk_and_interp env conj uu____77670 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____77699 =
      let uu____77700 =
        let uu____77708 =
          let uu____77709 = FStar_TypeChecker_Env.get_range env  in
          let uu____77710 =
            let uu____77721 =
              let uu____77722 =
                let uu____77727 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77727, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77722  in
            ([[l_and_a_b]], [aa; bb], uu____77721)  in
          FStar_SMTEncoding_Term.mkForall uu____77709 uu____77710  in
        (uu____77708, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77700  in
    [uu____77699]  in
  let mk_or_interp env disj uu____77782 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____77811 =
      let uu____77812 =
        let uu____77820 =
          let uu____77821 = FStar_TypeChecker_Env.get_range env  in
          let uu____77822 =
            let uu____77833 =
              let uu____77834 =
                let uu____77839 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77839, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77834  in
            ([[l_or_a_b]], [aa; bb], uu____77833)  in
          FStar_SMTEncoding_Term.mkForall uu____77821 uu____77822  in
        (uu____77820, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77812  in
    [uu____77811]  in
  let mk_eq2_interp env eq2 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____77917 =
      let uu____77918 =
        let uu____77926 =
          let uu____77927 = FStar_TypeChecker_Env.get_range env  in
          let uu____77928 =
            let uu____77939 =
              let uu____77940 =
                let uu____77945 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____77945, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77940  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____77939)  in
          FStar_SMTEncoding_Term.mkForall uu____77927 uu____77928  in
        (uu____77926, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77918  in
    [uu____77917]  in
  let mk_eq3_interp env eq3 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____78035 =
      let uu____78036 =
        let uu____78044 =
          let uu____78045 = FStar_TypeChecker_Env.get_range env  in
          let uu____78046 =
            let uu____78057 =
              let uu____78058 =
                let uu____78063 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78063, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78058  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78057)  in
          FStar_SMTEncoding_Term.mkForall uu____78045 uu____78046  in
        (uu____78044, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78036  in
    [uu____78035]  in
  let mk_imp_interp env imp tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____78163 =
      let uu____78164 =
        let uu____78172 =
          let uu____78173 = FStar_TypeChecker_Env.get_range env  in
          let uu____78174 =
            let uu____78185 =
              let uu____78186 =
                let uu____78191 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78191, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78186  in
            ([[l_imp_a_b]], [aa; bb], uu____78185)  in
          FStar_SMTEncoding_Term.mkForall uu____78173 uu____78174  in
        (uu____78172, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78164  in
    [uu____78163]  in
  let mk_iff_interp env iff tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____78275 =
      let uu____78276 =
        let uu____78284 =
          let uu____78285 = FStar_TypeChecker_Env.get_range env  in
          let uu____78286 =
            let uu____78297 =
              let uu____78298 =
                let uu____78303 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78303, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78298  in
            ([[l_iff_a_b]], [aa; bb], uu____78297)  in
          FStar_SMTEncoding_Term.mkForall uu____78285 uu____78286  in
        (uu____78284, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78276  in
    [uu____78275]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78374 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78374  in
    let uu____78379 =
      let uu____78380 =
        let uu____78388 =
          let uu____78389 = FStar_TypeChecker_Env.get_range env  in
          let uu____78390 =
            let uu____78401 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78401)  in
          FStar_SMTEncoding_Term.mkForall uu____78389 uu____78390  in
        (uu____78388, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78380  in
    [uu____78379]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78454 =
      let uu____78455 =
        let uu____78463 =
          let uu____78464 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78464 range_ty  in
        let uu____78465 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78463, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78465)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78455  in
    [uu____78454]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort)
       in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort)
       in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____78511 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78511 x1 t  in
      let uu____78513 = FStar_TypeChecker_Env.get_range env  in
      let uu____78514 =
        let uu____78525 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78525)  in
      FStar_SMTEncoding_Term.mkForall uu____78513 uu____78514  in
    let uu____78550 =
      let uu____78551 =
        let uu____78559 =
          let uu____78560 = FStar_TypeChecker_Env.get_range env  in
          let uu____78561 =
            let uu____78572 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78572)  in
          FStar_SMTEncoding_Term.mkForall uu____78560 uu____78561  in
        (uu____78559,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78551  in
    [uu____78550]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort)
       in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort)
       in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____78633 =
      let uu____78634 =
        let uu____78642 =
          let uu____78643 = FStar_TypeChecker_Env.get_range env  in
          let uu____78644 =
            let uu____78660 =
              let uu____78661 =
                let uu____78666 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78667 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78666, uu____78667)  in
              FStar_SMTEncoding_Util.mkAnd uu____78661  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78660)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78643 uu____78644  in
        (uu____78642,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78634  in
    [uu____78633]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.real_lid, mk_real);
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
          let uu____79225 =
            FStar_Util.find_opt
              (fun uu____79263  ->
                 match uu____79263 with
                 | (l,uu____79279) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79225 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79322,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79383 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79383 with
        | (form,decls) ->
            let uu____79392 =
              let uu____79395 =
                let uu____79398 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79398]  in
              FStar_All.pipe_right uu____79395
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79392
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____79457 =
                ((let uu____79461 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79461) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79457
              then
                let arg_sorts =
                  let uu____79473 =
                    let uu____79474 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79474.FStar_Syntax_Syntax.n  in
                  match uu____79473 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79480) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79518  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79525 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79527 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79527 with
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
                    let uu____79563 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79563, env1)
              else
                (let uu____79568 = prims.is lid  in
                 if uu____79568
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79577 = prims.mk lid vname  in
                   match uu____79577 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79601 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79601, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79610 =
                      let uu____79629 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79629 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79657 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79657
                            then
                              let uu____79662 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79665 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79665.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79665.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79665.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79665.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79665.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79665.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79665.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79665.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79665.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79665.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79665.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79665.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79665.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79665.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79665.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79665.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79665.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79665.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79665.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79665.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79665.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79665.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79665.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79665.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79665.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79665.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79665.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79665.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79665.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79665.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79665.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79665.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79665.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79665.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79665.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79665.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79665.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79665.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79665.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79665.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79665.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79665.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79662
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79688 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79688)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79610 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79794  ->
                                  match uu___639_79794 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79798 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79798 with
                                       | (uu____79831,xxv) ->
                                           let xx =
                                             let uu____79870 =
                                               let uu____79871 =
                                                 let uu____79877 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79877,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79871
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79870
                                              in
                                           let uu____79880 =
                                             let uu____79881 =
                                               let uu____79889 =
                                                 let uu____79890 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79891 =
                                                   let uu____79902 =
                                                     let uu____79903 =
                                                       let uu____79908 =
                                                         let uu____79909 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79909
                                                          in
                                                       (vapp, uu____79908)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79903
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79902)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79890 uu____79891
                                                  in
                                               (uu____79889,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79881
                                              in
                                           [uu____79880])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79924 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79924 with
                                       | (uu____79957,xxv) ->
                                           let xx =
                                             let uu____79996 =
                                               let uu____79997 =
                                                 let uu____80003 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____80003,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79997
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79996
                                              in
                                           let f1 =
                                             {
                                               FStar_Syntax_Syntax.ppname = f;
                                               FStar_Syntax_Syntax.index =
                                                 (Prims.parse_int "0");
                                               FStar_Syntax_Syntax.sort =
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
                                           let uu____80014 =
                                             let uu____80015 =
                                               let uu____80023 =
                                                 let uu____80024 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80025 =
                                                   let uu____80036 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80036)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80024 uu____80025
                                                  in
                                               (uu____80023,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80015
                                              in
                                           [uu____80014])
                                  | uu____80049 -> []))
                           in
                        let uu____80050 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80050 with
                         | (vars,guards,env',decls1,uu____80075) ->
                             let uu____80088 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80101 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80101, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80105 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80105 with
                                    | (g,ds) ->
                                        let uu____80118 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80118,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80088 with
                              | (guard,decls11) ->
                                  let dummy_var =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ("@dummy",
                                        FStar_SMTEncoding_Term.dummy_sort)
                                     in
                                  let dummy_tm =
                                    FStar_SMTEncoding_Term.mkFreeV dummy_var
                                      FStar_Range.dummyRange
                                     in
                                  let should_thunk uu____80141 =
                                    let is_type1 t =
                                      let uu____80149 =
                                        let uu____80150 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80150.FStar_Syntax_Syntax.n  in
                                      match uu____80149 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80154 -> true
                                      | uu____80156 -> false  in
                                    let is_squash1 t =
                                      let uu____80165 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80165 with
                                      | (head1,uu____80184) ->
                                          let uu____80209 =
                                            let uu____80210 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80210.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80209 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80215;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80216;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80218;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80219;_};_},uu____80220)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80228 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80233 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80233))
                                       &&
                                       (let uu____80239 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80239))
                                      &&
                                      (let uu____80242 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80242)
                                     in
                                  let uu____80244 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80303 -> (false, vars)  in
                                  (match uu____80244 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80353 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80353 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80389 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80398 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80398
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80409 ->
                                                  let uu____80418 =
                                                    let uu____80426 =
                                                      get_vtok ()  in
                                                    (uu____80426, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80418
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80433 =
                                                let uu____80441 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80441)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80433
                                               in
                                            let uu____80455 =
                                              let vname_decl =
                                                let uu____80463 =
                                                  let uu____80475 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80475,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80463
                                                 in
                                              let uu____80486 =
                                                let env2 =
                                                  let uu___1026_80492 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80492.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80493 =
                                                  let uu____80495 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80495
                                                   in
                                                if uu____80493
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80486 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80512 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80538 =
                                                          let uu____80541 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80541
                                                           in
                                                        let uu____80548 =
                                                          let uu____80549 =
                                                            let uu____80552 =
                                                              let uu____80553
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80553
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80557  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80557)
                                                              uu____80552
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80549
                                                           in
                                                        (uu____80538,
                                                          uu____80548)
                                                    | uu____80564 when
                                                        thunked ->
                                                        let uu____80575 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80575
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80590
                                                                 =
                                                                 let uu____80598
                                                                   =
                                                                   let uu____80601
                                                                    =
                                                                    let uu____80604
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80604]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80601
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80598)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80590
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80612
                                                               =
                                                               let uu____80620
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80620,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80612
                                                              in
                                                           let uu____80625 =
                                                             let uu____80628
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80628
                                                              in
                                                           (uu____80625,
                                                             env1))
                                                    | uu____80637 ->
                                                        let vtok =
                                                          get_vtok ()  in
                                                        let vtok_decl =
                                                          FStar_SMTEncoding_Term.DeclFun
                                                            (vtok, [],
                                                              FStar_SMTEncoding_Term.Term_sort,
                                                              FStar_Pervasives_Native.None)
                                                           in
                                                        let name_tok_corr_formula
                                                          pat =
                                                          let uu____80661 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80662 =
                                                            let uu____80673 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80673)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80661
                                                            uu____80662
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80683 =
                                                            let uu____80691 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80691,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80683
                                                           in
                                                        let tok_typing1 =
                                                          let ff =
                                                            FStar_SMTEncoding_Term.mk_fv
                                                              ("ty",
                                                                FStar_SMTEncoding_Term.Term_sort)
                                                             in
                                                          let f =
                                                            FStar_SMTEncoding_Util.mkFreeV
                                                              ff
                                                             in
                                                          let vtok_app_r =
                                                            let uu____80702 =
                                                              let uu____80703
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80703]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80702
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80730 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80731 =
                                                              let uu____80742
                                                                =
                                                                let uu____80743
                                                                  =
                                                                  let uu____80748
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80749
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80748,
                                                                    uu____80749)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80743
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80742)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80730
                                                              uu____80731
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80778 =
                                                          let uu____80781 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80781
                                                           in
                                                        (uu____80778, env1)
                                                     in
                                                  (match uu____80512 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80802 =
                                                         let uu____80805 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80805
                                                           tok_decl
                                                          in
                                                       (uu____80802, env2))
                                               in
                                            (match uu____80455 with
                                             | (decls2,env2) ->
                                                 let uu____80824 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80834 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80834 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80849 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80849, decls)
                                                    in
                                                 (match uu____80824 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80864 =
                                                          let uu____80872 =
                                                            let uu____80873 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80874 =
                                                              let uu____80885
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80885)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80873
                                                              uu____80874
                                                             in
                                                          (uu____80872,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80864
                                                         in
                                                      let freshness =
                                                        let uu____80901 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80901
                                                        then
                                                          let uu____80909 =
                                                            let uu____80910 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80911 =
                                                              let uu____80924
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____80931
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80924,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____80931)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80910
                                                              uu____80911
                                                             in
                                                          let uu____80937 =
                                                            let uu____80940 =
                                                              let uu____80941
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____80941
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____80940]  in
                                                          uu____80909 ::
                                                            uu____80937
                                                        else []  in
                                                      let g =
                                                        let uu____80947 =
                                                          let uu____80950 =
                                                            let uu____80953 =
                                                              let uu____80956
                                                                =
                                                                let uu____80959
                                                                  =
                                                                  let uu____80962
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____80962
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____80959
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____80956
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____80953
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80950
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____80947
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding *
            FStar_SMTEncoding_Term.decls_elt Prims.list *
            FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____81002 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____81002 with
          | FStar_Pervasives_Native.None  ->
              let uu____81013 = encode_free_var false env x t t_norm []  in
              (match uu____81013 with
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
            (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____81076 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81076 with
            | (decls,env1) ->
                let uu____81087 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81087
                then
                  let uu____81094 =
                    let uu____81095 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81095  in
                  (uu____81094, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_elt Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____81151  ->
                fun lb  ->
                  match uu____81151 with
                  | (decls,env1) ->
                      let uu____81171 =
                        let uu____81176 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81176
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81171 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81205 = FStar_Syntax_Util.head_and_args t  in
    match uu____81205 with
    | (hd1,args) ->
        let uu____81249 =
          let uu____81250 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81250.FStar_Syntax_Syntax.n  in
        (match uu____81249 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81256,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81280 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81291 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81299 = en  in
    let uu____81300 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81299.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81299.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81299.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81299.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81299.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81299.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81299.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81299.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81299.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81299.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81300
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81330  ->
      fun quals  ->
        match uu____81330 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81435 = FStar_Util.first_N nbinders formals  in
              match uu____81435 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81536  ->
                         fun uu____81537  ->
                           match (uu____81536, uu____81537) with
                           | ((formal,uu____81563),(binder,uu____81565)) ->
                               let uu____81586 =
                                 let uu____81593 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81593)  in
                               FStar_Syntax_Syntax.NT uu____81586) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81607 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81648  ->
                              match uu____81648 with
                              | (x,i) ->
                                  let uu____81667 =
                                    let uu___1139_81668 = x  in
                                    let uu____81669 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81668.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81668.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81669
                                    }  in
                                  (uu____81667, i)))
                       in
                    FStar_All.pipe_right uu____81607
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81693 =
                      let uu____81698 = FStar_Syntax_Subst.compress body  in
                      let uu____81699 =
                        let uu____81700 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81700
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81698
                        uu____81699
                       in
                    uu____81693 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81751 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81751.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81751.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81751.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81751.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81751.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81751.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81751.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81751.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81751.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81751.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81751.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81751.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81751.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81751.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81751.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81751.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81751.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81751.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81751.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81751.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81751.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81751.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81751.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81751.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81751.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81751.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81751.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81751.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81751.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81751.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81751.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81751.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81751.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81751.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81751.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81751.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81751.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81751.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81751.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81751.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81751.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81751.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81823  ->
                       fun uu____81824  ->
                         match (uu____81823, uu____81824) with
                         | ((x,uu____81850),(b,uu____81852)) ->
                             let uu____81873 =
                               let uu____81880 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81880)  in
                             FStar_Syntax_Syntax.NT uu____81873) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81905 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81905
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____81934 ->
                    let uu____81941 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____81941
                | uu____81942 when Prims.op_Negation norm1 ->
                    let t_norm =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Exclude
                          FStar_TypeChecker_Env.Zeta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.EraseUniverses] tcenv t2
                       in
                    arrow_formals_comp_norm true t_norm
                | uu____81945 ->
                    let uu____81946 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____81946)
                 in
              let aux t1 e1 =
                let uu____81988 = FStar_Syntax_Util.abs_formals e1  in
                match uu____81988 with
                | (binders,body,lopt) ->
                    let uu____82020 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82036 -> arrow_formals_comp_norm false t1  in
                    (match uu____82020 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82070 =
                           if nformals < nbinders
                           then
                             let uu____82114 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82114 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82198 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82198)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82238 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82238 with
                                | (binders1,body1) ->
                                    let uu____82291 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82291))
                             else
                               (let uu____82304 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82304))
                            in
                         (match uu____82070 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82364 = aux t e  in
              match uu____82364 with
              | (binders,body,comp) ->
                  let uu____82410 =
                    let uu____82421 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82421
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82436 = aux comp1 body1  in
                      match uu____82436 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82410 with
                   | (binders1,body1,comp1) ->
                       let uu____82519 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82519, comp1))
               in
            (try
               (fun uu___1216_82546  ->
                  match () with
                  | () ->
                      let uu____82553 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82553
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82569 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82632  ->
                                   fun lb  ->
                                     match uu____82632 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82687 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82687
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82693 =
                                             let uu____82702 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82702
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82693 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82569 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____82843;
                                    FStar_Syntax_Syntax.lbeff = uu____82844;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82846;
                                    FStar_Syntax_Syntax.lbpos = uu____82847;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82871 =
                                     let uu____82878 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82878 with
                                     | (tcenv',uu____82894,e_t) ->
                                         let uu____82900 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82911 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82900 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82928 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82928.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82871 with
                                    | (env',e1,t_norm1) ->
                                        let uu____82938 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____82938 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____82958 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____82958
                                               then
                                                 let uu____82963 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____82966 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____82963 uu____82966
                                               else ());
                                              (let uu____82971 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____82971 with
                                               | (vars,_guards,env'1,binder_decls,uu____82998)
                                                   ->
                                                   let uu____83011 =
                                                     if
                                                       fvb.FStar_SMTEncoding_Env.fvb_thunked
                                                         && (vars = [])
                                                     then
                                                       let dummy_var =
                                                         FStar_SMTEncoding_Term.mk_fv
                                                           ("@dummy",
                                                             FStar_SMTEncoding_Term.dummy_sort)
                                                          in
                                                       let dummy_tm =
                                                         FStar_SMTEncoding_Term.mkFreeV
                                                           dummy_var
                                                           FStar_Range.dummyRange
                                                          in
                                                       let app =
                                                         let uu____83028 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83028
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83050 =
                                                          let uu____83051 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83052 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83051 fvb
                                                            uu____83052
                                                           in
                                                        (vars, uu____83050))
                                                      in
                                                   (match uu____83011 with
                                                    | (vars1,app) ->
                                                        let uu____83063 =
                                                          let is_logical =
                                                            let uu____83076 =
                                                              let uu____83077
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83077.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83076
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83083 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83087 =
                                                              let uu____83088
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83088
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83087
                                                              (fun lid  ->
                                                                 let uu____83097
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83097
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83098 =
                                                            (Prims.op_Negation
                                                               is_prims)
                                                              &&
                                                              ((FStar_All.pipe_right
                                                                  quals
                                                                  (FStar_List.contains
                                                                    FStar_Syntax_Syntax.Logic))
                                                                 ||
                                                                 is_logical)
                                                             in
                                                          if uu____83098
                                                          then
                                                            let uu____83114 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83115 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83114,
                                                              uu____83115)
                                                          else
                                                            (let uu____83126
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83126))
                                                           in
                                                        (match uu____83063
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83150
                                                                 =
                                                                 let uu____83158
                                                                   =
                                                                   let uu____83159
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83160
                                                                    =
                                                                    let uu____83171
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83171)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83159
                                                                    uu____83160
                                                                    in
                                                                 let uu____83180
                                                                   =
                                                                   let uu____83181
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83181
                                                                    in
                                                                 (uu____83158,
                                                                   uu____83180,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83150
                                                                in
                                                             let uu____83187
                                                               =
                                                               let uu____83190
                                                                 =
                                                                 let uu____83193
                                                                   =
                                                                   let uu____83196
                                                                    =
                                                                    let uu____83199
                                                                    =
                                                                    let uu____83202
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83202
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83199
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83196
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83193
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83190
                                                                in
                                                             (uu____83187,
                                                               env2)))))))
                               | uu____83211 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83271 =
                                   let uu____83277 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83277,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83271  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83283 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83336  ->
                                         fun fvb  ->
                                           match uu____83336 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83391 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83391
                                                  in
                                               let gtok =
                                                 let uu____83395 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83395
                                                  in
                                               let env4 =
                                                 let uu____83398 =
                                                   let uu____83401 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83407  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83407) uu____83401
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83398
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83283 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83527
                                     t_norm uu____83529 =
                                     match (uu____83527, uu____83529) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83559;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83560;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83562;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83563;_})
                                         ->
                                         let uu____83590 =
                                           let uu____83597 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83597 with
                                           | (tcenv',uu____83613,e_t) ->
                                               let uu____83619 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83630 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83619 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83647 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83647.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83590 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83660 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83660
                                                then
                                                  let uu____83665 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83667 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83669 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83665 uu____83667
                                                    uu____83669
                                                else ());
                                               (let uu____83674 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83674 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83701 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83701 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83723 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83723
                                                           then
                                                             let uu____83728
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83730
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83733
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83735
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83728
                                                               uu____83730
                                                               uu____83733
                                                               uu____83735
                                                           else ());
                                                          (let uu____83740 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83740
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83769)
                                                               ->
                                                               let uu____83782
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83795,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83799
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83799
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83812
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83812,
                                                                    decls0))
                                                                  in
                                                               (match uu____83782
                                                                with
                                                                | (guard,guard_decls)
                                                                    ->
                                                                    let binder_decls1
                                                                    =
                                                                    FStar_List.append
                                                                    binder_decls
                                                                    guard_decls
                                                                     in
                                                                    let decl_g
                                                                    =
                                                                    let uu____83833
                                                                    =
                                                                    let uu____83845
                                                                    =
                                                                    let uu____83848
                                                                    =
                                                                    let uu____83851
                                                                    =
                                                                    let uu____83854
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83854
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83851
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83848
                                                                     in
                                                                    (g,
                                                                    uu____83845,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83833
                                                                     in
                                                                    let env02
                                                                    =
                                                                    FStar_SMTEncoding_Env.push_zfuel_name
                                                                    env01
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                    g  in
                                                                    let decl_g_tok
                                                                    =
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications"))
                                                                     in
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let rng =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let app =
                                                                    let uu____83884
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83884
                                                                     in
                                                                    let mk_g_app
                                                                    args =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    rng
                                                                    (FStar_Util.Inl
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    g))
                                                                    (fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    (Prims.parse_int "1"))
                                                                    args  in
                                                                    let gsapp
                                                                    =
                                                                    let uu____83899
                                                                    =
                                                                    let uu____83902
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83902
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83899
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83908
                                                                    =
                                                                    let uu____83911
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83911
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83908
                                                                     in
                                                                    let uu____83916
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83916
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____83932
                                                                    =
                                                                    let uu____83940
                                                                    =
                                                                    let uu____83941
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83942
                                                                    =
                                                                    let uu____83958
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    let uu____83964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____83964)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83959
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83958)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____83941
                                                                    uu____83942
                                                                     in
                                                                    let uu____83978
                                                                    =
                                                                    let uu____83979
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____83979
                                                                     in
                                                                    (uu____83940,
                                                                    uu____83978,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83932
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____83986
                                                                    =
                                                                    let uu____83994
                                                                    =
                                                                    let uu____83995
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83996
                                                                    =
                                                                    let uu____84007
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84007)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83995
                                                                    uu____83996
                                                                     in
                                                                    (uu____83994,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83986
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84021
                                                                    =
                                                                    let uu____84029
                                                                    =
                                                                    let uu____84030
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84031
                                                                    =
                                                                    let uu____84042
                                                                    =
                                                                    let uu____84043
                                                                    =
                                                                    let uu____84048
                                                                    =
                                                                    let uu____84049
                                                                    =
                                                                    let uu____84052
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84052
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84049
                                                                     in
                                                                    (gsapp,
                                                                    uu____84048)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84043
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84042)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84030
                                                                    uu____84031
                                                                     in
                                                                    (uu____84029,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84021
                                                                     in
                                                                    let uu____84066
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm)
                                                                     in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____84078
                                                                    =
                                                                    let uu____84079
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84079
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84078
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84081
                                                                    =
                                                                    let uu____84089
                                                                    =
                                                                    let uu____84090
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84091
                                                                    =
                                                                    let uu____84102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84102)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84090
                                                                    uu____84091
                                                                     in
                                                                    (uu____84089,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84081
                                                                     in
                                                                    let uu____84115
                                                                    =
                                                                    let uu____84124
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84124
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84139
                                                                    =
                                                                    let uu____84142
                                                                    =
                                                                    let uu____84143
                                                                    =
                                                                    let uu____84151
                                                                    =
                                                                    let uu____84152
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84153
                                                                    =
                                                                    let uu____84164
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84164)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84152
                                                                    uu____84153
                                                                     in
                                                                    (uu____84151,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84143
                                                                     in
                                                                    [uu____84142]
                                                                     in
                                                                    (d3,
                                                                    uu____84139)
                                                                     in
                                                                    match uu____84115
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84066
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84221
                                                                    =
                                                                    let uu____84224
                                                                    =
                                                                    let uu____84227
                                                                    =
                                                                    let uu____84230
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84230
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84227
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84224
                                                                     in
                                                                    let uu____84237
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84221,
                                                                    uu____84237,
                                                                    env02))))))))))
                                      in
                                   let uu____84242 =
                                     let uu____84255 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84318  ->
                                          fun uu____84319  ->
                                            match (uu____84318, uu____84319)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84444 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84444 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84255
                                      in
                                   (match uu____84242 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84511 =
                                          let isDeclFun uu___640_84528 =
                                            match uu___640_84528 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84530 -> true
                                            | uu____84543 -> false  in
                                          let uu____84545 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84545
                                            (fun decls3  ->
                                               let uu____84575 =
                                                 FStar_List.fold_left
                                                   (fun uu____84606  ->
                                                      fun elt  ->
                                                        match uu____84606
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84647 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84647
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84675
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84675
                                                               with
                                                               | (elt_decl_funs,elt_rest)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                    elts,
                                                                    (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___1459_84713
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84713.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84713.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84713.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84575 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84745 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84745, elts, rest))
                                           in
                                        (match uu____84511 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84774 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84780  ->
                                        match uu___641_84780 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84783 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84791 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84791)))
                                in
                             if uu____84774
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84813  ->
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
                   let uu____84852 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84852
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84871 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84871, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84927 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84927 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____84933 = encode_sigelt' env se  in
      match uu____84933 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____84945 =
                  let uu____84948 =
                    let uu____84949 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____84949  in
                  [uu____84948]  in
                FStar_All.pipe_right uu____84945
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____84954 ->
                let uu____84955 =
                  let uu____84958 =
                    let uu____84961 =
                      let uu____84962 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____84962  in
                    [uu____84961]  in
                  FStar_All.pipe_right uu____84958
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____84969 =
                  let uu____84972 =
                    let uu____84975 =
                      let uu____84978 =
                        let uu____84979 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____84979  in
                      [uu____84978]  in
                    FStar_All.pipe_right uu____84975
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____84972  in
                FStar_List.append uu____84955 uu____84969
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____84993 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____84993
       then
         let uu____84998 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____84998
       else ());
      (let is_opaque_to_smt t =
         let uu____85010 =
           let uu____85011 = FStar_Syntax_Subst.compress t  in
           uu____85011.FStar_Syntax_Syntax.n  in
         match uu____85010 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85016)) -> s = "opaque_to_smt"
         | uu____85021 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85030 =
           let uu____85031 = FStar_Syntax_Subst.compress t  in
           uu____85031.FStar_Syntax_Syntax.n  in
         match uu____85030 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85036)) -> s = "uninterpreted_by_smt"
         | uu____85041 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85047 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85053 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85065 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85066 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85067 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85080 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85082 =
             let uu____85084 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85084  in
           if uu____85082
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85113 ->
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
                let uu____85145 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85145 with
                | (formals,uu____85165) ->
                    let arity = FStar_List.length formals  in
                    let uu____85189 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85189 with
                     | (aname,atok,env2) ->
                         let uu____85215 =
                           let uu____85220 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85220 env2
                            in
                         (match uu____85215 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85232 =
                                  let uu____85233 =
                                    let uu____85245 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85265  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85245,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85233
                                   in
                                [uu____85232;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85282 =
                                let aux uu____85328 uu____85329 =
                                  match (uu____85328, uu____85329) with
                                  | ((bv,uu____85373),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85405 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85405 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85428 =
                                             let uu____85431 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85431 :: acc_sorts  in
                                           (env4, uu____85428, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85282 with
                               | (uu____85463,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85479 =
                                       let uu____85487 =
                                         let uu____85488 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85489 =
                                           let uu____85500 =
                                             let uu____85501 =
                                               let uu____85506 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85506)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85501
                                              in
                                           ([[app]], xs_sorts, uu____85500)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85488 uu____85489
                                          in
                                       (uu____85487,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85479
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85521 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85521
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85524 =
                                       let uu____85532 =
                                         let uu____85533 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85534 =
                                           let uu____85545 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85545)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85533 uu____85534
                                          in
                                       (uu____85532,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85524
                                      in
                                   let uu____85558 =
                                     let uu____85561 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85561  in
                                   (env2, uu____85558))))
                 in
              let uu____85570 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85570 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85596,uu____85597)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85598 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85598 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85620,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85627 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85633  ->
                       match uu___642_85633 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85636 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85642 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85645 -> false))
                in
             Prims.op_Negation uu____85627  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85655 =
                let uu____85660 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85660 env fv t quals  in
              match uu____85655 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85674 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85674  in
                  let uu____85677 =
                    let uu____85678 =
                      let uu____85681 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85681
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85678  in
                  (uu____85677, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85691 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85691 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85703 = env  in
                  let uu____85704 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85703.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85703.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85703.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85704;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85703.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85703.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85703.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85703.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85703.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85703.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85703.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85706 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85706 with
                 | (f3,decls) ->
                     let g =
                       let uu____85720 =
                         let uu____85723 =
                           let uu____85724 =
                             let uu____85732 =
                               let uu____85733 =
                                 let uu____85735 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85735
                                  in
                               FStar_Pervasives_Native.Some uu____85733  in
                             let uu____85739 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85732, uu____85739)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85724  in
                         [uu____85723]  in
                       FStar_All.pipe_right uu____85720
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85748) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85762 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85784 =
                        let uu____85787 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85787.FStar_Syntax_Syntax.fv_name  in
                      uu____85784.FStar_Syntax_Syntax.v  in
                    let uu____85788 =
                      let uu____85790 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85790  in
                    if uu____85788
                    then
                      let val_decl =
                        let uu___1629_85822 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85822.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85822.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85822.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85823 = encode_sigelt' env1 val_decl  in
                      match uu____85823 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85762 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85859,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85861;
                           FStar_Syntax_Syntax.lbtyp = uu____85862;
                           FStar_Syntax_Syntax.lbeff = uu____85863;
                           FStar_Syntax_Syntax.lbdef = uu____85864;
                           FStar_Syntax_Syntax.lbattrs = uu____85865;
                           FStar_Syntax_Syntax.lbpos = uu____85866;_}::[]),uu____85867)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85886 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85886 with
            | (tname,ttok,env1) ->
                let xx =
                  FStar_SMTEncoding_Term.mk_fv
                    ("x", FStar_SMTEncoding_Term.Term_sort)
                   in
                let x = FStar_SMTEncoding_Util.mkFreeV xx  in
                let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                   in
                let valid_b2t_x =
                  FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
                let decls =
                  let uu____85924 =
                    let uu____85927 =
                      let uu____85928 =
                        let uu____85936 =
                          let uu____85937 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____85938 =
                            let uu____85949 =
                              let uu____85950 =
                                let uu____85955 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____85955)  in
                              FStar_SMTEncoding_Util.mkEq uu____85950  in
                            ([[b2t_x]], [xx], uu____85949)  in
                          FStar_SMTEncoding_Term.mkForall uu____85937
                            uu____85938
                           in
                        (uu____85936,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85928  in
                    [uu____85927]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85924
                   in
                let uu____85993 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____85993, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____85996,uu____85997) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86007  ->
                   match uu___643_86007 with
                   | FStar_Syntax_Syntax.Discriminator uu____86009 -> true
                   | uu____86011 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86013,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86025 =
                      let uu____86027 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86027.FStar_Ident.idText  in
                    uu____86025 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86034  ->
                      match uu___644_86034 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86037 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86040) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86054  ->
                   match uu___645_86054 with
                   | FStar_Syntax_Syntax.Projector uu____86056 -> true
                   | uu____86062 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86066 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86066 with
            | FStar_Pervasives_Native.Some uu____86073 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86075 = se  in
                  let uu____86076 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86076;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86075.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86075.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86075.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86079) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86094) ->
           let uu____86103 = encode_sigelts env ses  in
           (match uu____86103 with
            | (g,env1) ->
                let uu____86114 =
                  FStar_List.fold_left
                    (fun uu____86138  ->
                       fun elt  ->
                         match uu____86138 with
                         | (g',inversions) ->
                             let uu____86166 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86189  ->
                                       match uu___646_86189 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86191;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86192;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86193;_}
                                           -> false
                                       | uu____86200 -> true))
                                in
                             (match uu____86166 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86225 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86225.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86225.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86225.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86114 with
                 | (g',inversions) ->
                     let uu____86244 =
                       FStar_List.fold_left
                         (fun uu____86275  ->
                            fun elt  ->
                              match uu____86275 with
                              | (decls,elts,rest) ->
                                  let uu____86316 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86325  ->
                                            match uu___647_86325 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86327 -> true
                                            | uu____86340 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86316
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86363 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86384  ->
                                               match uu___648_86384 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86386 -> true
                                               | uu____86399 -> false))
                                        in
                                     match uu____86363 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86430 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86430.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86430.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86430.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86244 with
                      | (decls,elts,rest) ->
                          let uu____86456 =
                            let uu____86457 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86464 =
                              let uu____86467 =
                                let uu____86470 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86470  in
                              FStar_List.append elts uu____86467  in
                            FStar_List.append uu____86457 uu____86464  in
                          (uu____86456, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86481,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86494 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86494 with
             | (usubst,uvs) ->
                 let uu____86514 =
                   let uu____86521 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86522 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86523 =
                     let uu____86524 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86524 k  in
                   (uu____86521, uu____86522, uu____86523)  in
                 (match uu____86514 with
                  | (env1,tps1,k1) ->
                      let uu____86537 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86537 with
                       | (tps2,k2) ->
                           let uu____86545 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86545 with
                            | (uu____86561,k3) ->
                                let uu____86583 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86583 with
                                 | (tps3,env_tps,uu____86595,us) ->
                                     let u_k =
                                       let uu____86598 =
                                         let uu____86599 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86600 =
                                           let uu____86605 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86607 =
                                             let uu____86608 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86608
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86605 uu____86607
                                            in
                                         uu____86600
                                           FStar_Pervasives_Native.None
                                           uu____86599
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86598 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86628) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86634,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86637) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86645,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86652) ->
                                           let uu____86653 =
                                             let uu____86655 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86655
                                              in
                                           failwith uu____86653
                                       | (uu____86659,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86660 =
                                             let uu____86662 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86662
                                              in
                                           failwith uu____86660
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86666,uu____86667) ->
                                           let uu____86676 =
                                             let uu____86678 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86678
                                              in
                                           failwith uu____86676
                                       | (uu____86682,FStar_Syntax_Syntax.U_unif
                                          uu____86683) ->
                                           let uu____86692 =
                                             let uu____86694 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86694
                                              in
                                           failwith uu____86692
                                       | uu____86698 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86711 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86711 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86729 = u_leq_u_k u_tp  in
                                       if uu____86729
                                       then true
                                       else
                                         (let uu____86736 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86736 with
                                          | (formals,uu____86753) ->
                                              let uu____86774 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86774 with
                                               | (uu____86784,uu____86785,uu____86786,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86797 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86797
             then
               let uu____86802 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86802
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86822  ->
                       match uu___649_86822 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86826 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86839 = c  in
                 match uu____86839 with
                 | (name,args,uu____86844,uu____86845,uu____86846) ->
                     let uu____86857 =
                       let uu____86858 =
                         let uu____86870 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86897  ->
                                   match uu____86897 with
                                   | (uu____86906,sort,uu____86908) -> sort))
                            in
                         (name, uu____86870,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86858  in
                     [uu____86857]
               else
                 (let uu____86919 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____86919 c)
                in
             let inversion_axioms tapp vars =
               let uu____86937 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____86945 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____86945 FStar_Option.isNone))
                  in
               if uu____86937
               then []
               else
                 (let uu____86980 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____86980 with
                  | (xxsym,xx) ->
                      let uu____86993 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87032  ->
                                fun l  ->
                                  match uu____87032 with
                                  | (out,decls) ->
                                      let uu____87052 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87052 with
                                       | (uu____87063,data_t) ->
                                           let uu____87065 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87065 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87109 =
                                                    let uu____87110 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87110.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87109 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87113,indices)
                                                      -> indices
                                                  | uu____87139 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87169  ->
                                                            match uu____87169
                                                            with
                                                            | (x,uu____87177)
                                                                ->
                                                                let uu____87182
                                                                  =
                                                                  let uu____87183
                                                                    =
                                                                    let uu____87191
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87191,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87183
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87182)
                                                       env)
                                                   in
                                                let uu____87196 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87196 with
                                                 | (indices1,decls') ->
                                                     (if
                                                        (FStar_List.length
                                                           indices1)
                                                          <>
                                                          (FStar_List.length
                                                             vars)
                                                      then
                                                        failwith "Impossible"
                                                      else ();
                                                      (let eqs =
                                                         if is_injective
                                                         then
                                                           FStar_List.map2
                                                             (fun v1  ->
                                                                fun a  ->
                                                                  let uu____87231
                                                                    =
                                                                    let uu____87236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87236,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87231)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87239 =
                                                         let uu____87240 =
                                                           let uu____87245 =
                                                             let uu____87246
                                                               =
                                                               let uu____87251
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87252
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87251,
                                                                 uu____87252)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87246
                                                              in
                                                           (out, uu____87245)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87240
                                                          in
                                                       (uu____87239,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____86993 with
                       | (data_ax,decls) ->
                           let uu____87267 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87267 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87284 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87284 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87291 =
                                    let uu____87299 =
                                      let uu____87300 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87301 =
                                        let uu____87312 =
                                          let uu____87313 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87315 =
                                            let uu____87318 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87318 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87313 uu____87315
                                           in
                                        let uu____87320 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87312,
                                          uu____87320)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87300 uu____87301
                                       in
                                    let uu____87329 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87299,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87329)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87291
                                   in
                                let uu____87335 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87335)))
                in
             let uu____87342 =
               let uu____87347 =
                 let uu____87348 = FStar_Syntax_Subst.compress k  in
                 uu____87348.FStar_Syntax_Syntax.n  in
               match uu____87347 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87383 -> (tps, k)  in
             match uu____87342 with
             | (formals,res) ->
                 let uu____87390 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87390 with
                  | (formals1,res1) ->
                      let uu____87401 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87401 with
                       | (vars,guards,env',binder_decls,uu____87426) ->
                           let arity = FStar_List.length vars  in
                           let uu____87440 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87440 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87470 =
                                    let uu____87478 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87478)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87470
                                   in
                                let uu____87484 =
                                  let tname_decl =
                                    let uu____87494 =
                                      let uu____87495 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87514 =
                                                  let uu____87516 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87516
                                                   in
                                                let uu____87518 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87514, uu____87518,
                                                  false)))
                                         in
                                      let uu____87522 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87495,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87522, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87494
                                     in
                                  let uu____87530 =
                                    match vars with
                                    | [] ->
                                        let uu____87543 =
                                          let uu____87544 =
                                            let uu____87547 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87553  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87553) uu____87547
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87544
                                           in
                                        ([], uu____87543)
                                    | uu____87560 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87570 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87570
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87586 =
                                            let uu____87594 =
                                              let uu____87595 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87596 =
                                                let uu____87612 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87612)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87595 uu____87596
                                               in
                                            (uu____87594,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87586
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87530 with
                                  | (tok_decls,env2) ->
                                      let uu____87639 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87639
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87484 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87667 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87667 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87689 =
                                                 let uu____87690 =
                                                   let uu____87698 =
                                                     let uu____87699 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87699
                                                      in
                                                   (uu____87698,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87690
                                                  in
                                               [uu____87689]
                                             else []  in
                                           let uu____87707 =
                                             let uu____87710 =
                                               let uu____87713 =
                                                 let uu____87716 =
                                                   let uu____87717 =
                                                     let uu____87725 =
                                                       let uu____87726 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87727 =
                                                         let uu____87738 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87738)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87726
                                                         uu____87727
                                                        in
                                                     (uu____87725,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87717
                                                    in
                                                 [uu____87716]  in
                                               FStar_List.append karr
                                                 uu____87713
                                                in
                                             FStar_All.pipe_right uu____87710
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87707
                                        in
                                     let aux =
                                       let uu____87757 =
                                         let uu____87760 =
                                           inversion_axioms tapp vars  in
                                         let uu____87763 =
                                           let uu____87766 =
                                             let uu____87769 =
                                               let uu____87770 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87770 env2
                                                 tapp vars
                                                in
                                             [uu____87769]  in
                                           FStar_All.pipe_right uu____87766
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87760
                                           uu____87763
                                          in
                                       FStar_List.append kindingAx
                                         uu____87757
                                        in
                                     let g =
                                       let uu____87778 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87778
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87786,uu____87787,uu____87788,uu____87789,uu____87790)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87798,t,uu____87800,n_tps,uu____87802) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87812 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87812 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87860 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87860 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87888 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87888 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____87908 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____87908 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____87987 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____87987,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____87994 =
                                   let uu____87995 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____87995, true)
                                    in
                                 let uu____88003 =
                                   let uu____88010 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88010
                                    in
                                 FStar_All.pipe_right uu____87994 uu____88003
                                  in
                               let app =
                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                   ddtok_tm vars
                                  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let xvars =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               let dapp =
                                 FStar_SMTEncoding_Util.mkApp
                                   (ddconstrsym, xvars)
                                  in
                               let uu____88022 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88022 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88034::uu____88035 ->
                                          let ff =
                                            FStar_SMTEncoding_Term.mk_fv
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
                                            let uu____88084 =
                                              let uu____88085 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88085]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88084
                                             in
                                          let uu____88111 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88112 =
                                            let uu____88123 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88123)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88111 uu____88112
                                      | uu____88150 -> tok_typing  in
                                    let uu____88161 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88161 with
                                     | (vars',guards',env'',decls_formals,uu____88186)
                                         ->
                                         let uu____88199 =
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
                                         (match uu____88199 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88229 ->
                                                    let uu____88238 =
                                                      let uu____88239 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88239
                                                       in
                                                    [uu____88238]
                                                 in
                                              let encode_elim uu____88255 =
                                                let uu____88256 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88256 with
                                                | (head1,args) ->
                                                    let uu____88307 =
                                                      let uu____88308 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88308.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88307 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88320;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88321;_},uu____88322)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88328 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88328
                                                          with
                                                          | (encoded_args,arg_decls)
                                                              ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____88391
                                                                    ->
                                                                    let uu____88392
                                                                    =
                                                                    let uu____88398
                                                                    =
                                                                    let uu____88400
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88400
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88398)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88392
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88423
                                                                    =
                                                                    let uu____88425
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88425
                                                                     in
                                                                    if
                                                                    uu____88423
                                                                    then
                                                                    let uu____88447
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88447]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88450
                                                                =
                                                                let uu____88464
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88521
                                                                     ->
                                                                    fun
                                                                    uu____88522
                                                                     ->
                                                                    match 
                                                                    (uu____88521,
                                                                    uu____88522)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88633
                                                                    =
                                                                    let uu____88641
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88641
                                                                     in
                                                                    (match uu____88633
                                                                    with
                                                                    | 
                                                                    (uu____88655,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88666
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88666
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88671
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88671
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____88464
                                                                 in
                                                              (match uu____88450
                                                               with
                                                               | (uu____88692,arg_vars,elim_eqns_or_guards,uu____88695)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
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
                                                                    let uu____88722
                                                                    =
                                                                    let uu____88730
                                                                    =
                                                                    let uu____88731
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88732
                                                                    =
                                                                    let uu____88743
                                                                    =
                                                                    let uu____88744
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88744
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88746
                                                                    =
                                                                    let uu____88747
                                                                    =
                                                                    let uu____88752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88752)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88747
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88743,
                                                                    uu____88746)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88731
                                                                    uu____88732
                                                                     in
                                                                    (uu____88730,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88722
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88767
                                                                    =
                                                                    let uu____88768
                                                                    =
                                                                    let uu____88774
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88774,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88768
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88767
                                                                     in
                                                                    let uu____88777
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88777
                                                                    then
                                                                    let x =
                                                                    let uu____88781
                                                                    =
                                                                    let uu____88787
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88787,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88781
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88792
                                                                    =
                                                                    let uu____88800
                                                                    =
                                                                    let uu____88801
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88802
                                                                    =
                                                                    let uu____88813
                                                                    =
                                                                    let uu____88818
                                                                    =
                                                                    let uu____88821
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88821]
                                                                     in
                                                                    [uu____88818]
                                                                     in
                                                                    let uu____88826
                                                                    =
                                                                    let uu____88827
                                                                    =
                                                                    let uu____88832
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88834
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88832,
                                                                    uu____88834)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88827
                                                                     in
                                                                    (uu____88813,
                                                                    [x],
                                                                    uu____88826)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88801
                                                                    uu____88802
                                                                     in
                                                                    let uu____88855
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88800,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88855)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88792
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88866
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
                                                                    (let uu____88889
                                                                    =
                                                                    let uu____88890
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88890
                                                                    dapp1  in
                                                                    [uu____88889])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88866
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88897
                                                                    =
                                                                    let uu____88905
                                                                    =
                                                                    let uu____88906
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88907
                                                                    =
                                                                    let uu____88918
                                                                    =
                                                                    let uu____88919
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88919
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88921
                                                                    =
                                                                    let uu____88922
                                                                    =
                                                                    let uu____88927
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88927)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88922
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88918,
                                                                    uu____88921)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88906
                                                                    uu____88907
                                                                     in
                                                                    (uu____88905,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88897)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88946 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88946
                                                          with
                                                          | (encoded_args,arg_decls)
                                                              ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____89009
                                                                    ->
                                                                    let uu____89010
                                                                    =
                                                                    let uu____89016
                                                                    =
                                                                    let uu____89018
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89018
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89016)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89010
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89041
                                                                    =
                                                                    let uu____89043
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89043
                                                                     in
                                                                    if
                                                                    uu____89041
                                                                    then
                                                                    let uu____89065
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89065]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89068
                                                                =
                                                                let uu____89082
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89139
                                                                     ->
                                                                    fun
                                                                    uu____89140
                                                                     ->
                                                                    match 
                                                                    (uu____89139,
                                                                    uu____89140)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89251
                                                                    =
                                                                    let uu____89259
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89259
                                                                     in
                                                                    (match uu____89251
                                                                    with
                                                                    | 
                                                                    (uu____89273,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89284
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89284
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89289
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89289
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____89082
                                                                 in
                                                              (match uu____89068
                                                               with
                                                               | (uu____89310,arg_vars,elim_eqns_or_guards,uu____89313)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
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
                                                                    let uu____89340
                                                                    =
                                                                    let uu____89348
                                                                    =
                                                                    let uu____89349
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89350
                                                                    =
                                                                    let uu____89361
                                                                    =
                                                                    let uu____89362
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89362
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89364
                                                                    =
                                                                    let uu____89365
                                                                    =
                                                                    let uu____89370
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89370)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89365
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89361,
                                                                    uu____89364)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89349
                                                                    uu____89350
                                                                     in
                                                                    (uu____89348,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89340
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89385
                                                                    =
                                                                    let uu____89386
                                                                    =
                                                                    let uu____89392
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89392,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89386
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89385
                                                                     in
                                                                    let uu____89395
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89395
                                                                    then
                                                                    let x =
                                                                    let uu____89399
                                                                    =
                                                                    let uu____89405
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89405,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89399
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89410
                                                                    =
                                                                    let uu____89418
                                                                    =
                                                                    let uu____89419
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89420
                                                                    =
                                                                    let uu____89431
                                                                    =
                                                                    let uu____89436
                                                                    =
                                                                    let uu____89439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89439]
                                                                     in
                                                                    [uu____89436]
                                                                     in
                                                                    let uu____89444
                                                                    =
                                                                    let uu____89445
                                                                    =
                                                                    let uu____89450
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89452
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89450,
                                                                    uu____89452)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89445
                                                                     in
                                                                    (uu____89431,
                                                                    [x],
                                                                    uu____89444)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89419
                                                                    uu____89420
                                                                     in
                                                                    let uu____89473
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89418,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89473)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89410
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89484
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
                                                                    (let uu____89507
                                                                    =
                                                                    let uu____89508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89508
                                                                    dapp1  in
                                                                    [uu____89507])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89484
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89515
                                                                    =
                                                                    let uu____89523
                                                                    =
                                                                    let uu____89524
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89525
                                                                    =
                                                                    let uu____89536
                                                                    =
                                                                    let uu____89537
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89537
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89539
                                                                    =
                                                                    let uu____89540
                                                                    =
                                                                    let uu____89545
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89545)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89540
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89536,
                                                                    uu____89539)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89524
                                                                    uu____89525
                                                                     in
                                                                    (uu____89523,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89515)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89562 ->
                                                         ((let uu____89564 =
                                                             let uu____89570
                                                               =
                                                               let uu____89572
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89574
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89572
                                                                 uu____89574
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89570)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89564);
                                                          ([], [])))
                                                 in
                                              let uu____89582 =
                                                encode_elim ()  in
                                              (match uu____89582 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89608 =
                                                       let uu____89611 =
                                                         let uu____89614 =
                                                           let uu____89617 =
                                                             let uu____89620
                                                               =
                                                               let uu____89623
                                                                 =
                                                                 let uu____89626
                                                                   =
                                                                   let uu____89627
                                                                    =
                                                                    let uu____89639
                                                                    =
                                                                    let uu____89640
                                                                    =
                                                                    let uu____89642
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89642
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89640
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89639)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89627
                                                                    in
                                                                 [uu____89626]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89623
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89620
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89653 =
                                                             let uu____89656
                                                               =
                                                               let uu____89659
                                                                 =
                                                                 let uu____89662
                                                                   =
                                                                   let uu____89665
                                                                    =
                                                                    let uu____89668
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89673
                                                                    =
                                                                    let uu____89676
                                                                    =
                                                                    let uu____89677
                                                                    =
                                                                    let uu____89685
                                                                    =
                                                                    let uu____89686
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89687
                                                                    =
                                                                    let uu____89698
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89698)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89686
                                                                    uu____89687
                                                                     in
                                                                    (uu____89685,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89677
                                                                     in
                                                                    let uu____89711
                                                                    =
                                                                    let uu____89714
                                                                    =
                                                                    let uu____89715
                                                                    =
                                                                    let uu____89723
                                                                    =
                                                                    let uu____89724
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89725
                                                                    =
                                                                    let uu____89736
                                                                    =
                                                                    let uu____89737
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89737
                                                                    vars'  in
                                                                    let uu____89739
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89736,
                                                                    uu____89739)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89724
                                                                    uu____89725
                                                                     in
                                                                    (uu____89723,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89715
                                                                     in
                                                                    [uu____89714]
                                                                     in
                                                                    uu____89676
                                                                    ::
                                                                    uu____89711
                                                                     in
                                                                    uu____89668
                                                                    ::
                                                                    uu____89673
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89665
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89662
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89659
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89656
                                                              in
                                                           FStar_List.append
                                                             uu____89617
                                                             uu____89653
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89614
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89611
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89608
                                                      in
                                                   let uu____89756 =
                                                     let uu____89757 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89757 g
                                                      in
                                                   (uu____89756, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89791  ->
              fun se  ->
                match uu____89791 with
                | (g,env1) ->
                    let uu____89811 = encode_sigelt env1 se  in
                    (match uu____89811 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89879 =
        match uu____89879 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____89916 ->
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
                 ((let uu____89924 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____89924
                   then
                     let uu____89929 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____89931 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____89933 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____89929 uu____89931 uu____89933
                   else ());
                  (let uu____89938 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____89938 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____89956 =
                         let uu____89964 =
                           let uu____89966 =
                             let uu____89968 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____89968
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____89966  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____89964
                          in
                       (match uu____89956 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____89988 = FStar_Options.log_queries ()
                                 in
                              if uu____89988
                              then
                                let uu____89991 =
                                  let uu____89993 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____89995 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____89997 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____89993 uu____89995 uu____89997
                                   in
                                FStar_Pervasives_Native.Some uu____89991
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90013 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90023 =
                                let uu____90026 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90026  in
                              FStar_List.append uu____90013 uu____90023  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90038,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90058 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90058 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90079 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90079 with | (uu____90106,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90159  ->
              match uu____90159 with
              | (l,uu____90168,uu____90169) ->
                  let uu____90172 =
                    let uu____90184 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90184, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90172))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90217  ->
              match uu____90217 with
              | (l,uu____90228,uu____90229) ->
                  let uu____90232 =
                    let uu____90233 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90236  -> FStar_SMTEncoding_Term.Echo _90236)
                      uu____90233
                     in
                  let uu____90237 =
                    let uu____90240 =
                      let uu____90241 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90241  in
                    [uu____90240]  in
                  uu____90232 :: uu____90237))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90270 =
      let uu____90273 =
        let uu____90274 = FStar_Util.psmap_empty ()  in
        let uu____90289 =
          let uu____90298 = FStar_Util.psmap_empty ()  in (uu____90298, [])
           in
        let uu____90305 =
          let uu____90307 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90307 FStar_Ident.string_of_lid  in
        let uu____90309 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90274;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90289;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90305;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90309
        }  in
      [uu____90273]  in
    FStar_ST.op_Colon_Equals last_env uu____90270
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90353 = FStar_ST.op_Bang last_env  in
      match uu____90353 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90381 ->
          let uu___2175_90384 = e  in
          let uu____90385 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90384.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90384.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90384.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90384.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90384.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90384.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90384.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90385;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90384.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90384.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90393 = FStar_ST.op_Bang last_env  in
    match uu____90393 with
    | [] -> failwith "Empty env stack"
    | uu____90420::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90452  ->
    let uu____90453 = FStar_ST.op_Bang last_env  in
    match uu____90453 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90513  ->
    let uu____90514 = FStar_ST.op_Bang last_env  in
    match uu____90514 with
    | [] -> failwith "Popping an empty stack"
    | uu____90541::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90578  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90631  ->
         let uu____90632 = snapshot_env ()  in
         match uu____90632 with
         | (env_depth,()) ->
             let uu____90654 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90654 with
              | (varops_depth,()) ->
                  let uu____90676 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90676 with
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
        (fun uu____90734  ->
           let uu____90735 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90735 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90830 = snapshot msg  in () 
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
        | (uu____90876::uu____90877,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90885 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90885.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90885.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90885.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90886 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_90913 = elt  in
        let uu____90914 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_90913.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_90913.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____90914;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_90913.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____90934 =
        let uu____90937 =
          let uu____90938 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____90938  in
        let uu____90939 = open_fact_db_tags env  in uu____90937 ::
          uu____90939
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____90934
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_elt Prims.list *
        FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____90966 = encode_sigelt env se  in
      match uu____90966 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (recover_caching_and_update_env :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun decls  ->
      FStar_All.pipe_right decls
        (FStar_List.collect
           (fun elt  ->
              if
                elt.FStar_SMTEncoding_Term.key = FStar_Pervasives_Native.None
              then [elt]
              else
                (let uu____91012 =
                   let uu____91015 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91015
                    in
                 match uu____91012 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91030 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91030
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91060 = FStar_Options.log_queries ()  in
        if uu____91060
        then
          let uu____91065 =
            let uu____91066 =
              let uu____91068 =
                let uu____91070 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91070 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91068  in
            FStar_SMTEncoding_Term.Caption uu____91066  in
          uu____91065 :: decls
        else decls  in
      (let uu____91089 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91089
       then
         let uu____91092 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91092
       else ());
      (let env =
         let uu____91098 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91098 tcenv  in
       let uu____91099 = encode_top_level_facts env se  in
       match uu____91099 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91113 =
               let uu____91116 =
                 let uu____91119 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91119
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91116  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91113)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91152 = FStar_Options.log_queries ()  in
          if uu____91152
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91172 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91172.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91172.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91172.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91172.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91172.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91172.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91172.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91172.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91172.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91172.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91177 =
             let uu____91180 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91180
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91177  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91200 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91200
      then ([], [])
      else
        (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh ();
         (let name =
            FStar_Util.format2 "%s %s"
              (if modul.FStar_Syntax_Syntax.is_interface
               then "interface"
               else "module")
              (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
             in
          (let uu____91224 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91224
           then
             let uu____91227 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91227
           else ());
          (let env =
             let uu____91235 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91235
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91274  ->
                     fun se  ->
                       match uu____91274 with
                       | (g,env2) ->
                           let uu____91294 = encode_top_level_facts env2 se
                              in
                           (match uu____91294 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91317 =
             encode_signature
               (let uu___2303_91326 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91326.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91326.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91326.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91326.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91326.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91326.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91326.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91326.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91326.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91326.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91317 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91342 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91342
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91348 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91348))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91376  ->
        match uu____91376 with
        | (decls,fvbs) ->
            ((let uu____91390 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91390
              then ()
              else
                (let uu____91395 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91395
                 then
                   let uu____91398 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91398
                 else ()));
             (let env =
                let uu____91406 = get_env name tcenv  in
                FStar_All.pipe_right uu____91406
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91408 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91408
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91422 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91422
               then
                 FStar_Util.print1
                   "Done encoding externals from cache for %s\n"
                   name.FStar_Ident.str
               else ())))
  
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
        (let uu____91484 =
           let uu____91486 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91486.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91484);
        (let env =
           let uu____91488 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91488 tcenv  in
         let uu____91489 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91528 = aux rest  in
                 (match uu____91528 with
                  | (out,rest1) ->
                      let t =
                        let uu____91556 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91556 with
                        | FStar_Pervasives_Native.Some uu____91559 ->
                            let uu____91560 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91560
                              x.FStar_Syntax_Syntax.sort
                        | uu____91561 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91565 =
                        let uu____91568 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91571 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91571.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91571.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91568 :: out  in
                      (uu____91565, rest1))
             | uu____91576 -> ([], bindings)  in
           let uu____91583 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91583 with
           | (closing,bindings) ->
               let uu____91610 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91610, bindings)
            in
         match uu____91489 with
         | (q1,bindings) ->
             let uu____91641 = encode_env_bindings env bindings  in
             (match uu____91641 with
              | (env_decls,env1) ->
                  ((let uu____91663 =
                      ((FStar_TypeChecker_Env.debug tcenv
                          FStar_Options.Medium)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____91663
                    then
                      let uu____91670 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91670
                    else ());
                   (let uu____91675 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91675 with
                    | (phi,qdecls) ->
                        let uu____91696 =
                          let uu____91701 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91701 phi
                           in
                        (match uu____91696 with
                         | (labels,phi1) ->
                             let uu____91718 = encode_labels labels  in
                             (match uu____91718 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91754 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91754
                                    then
                                      let uu____91759 =
                                        let uu____91760 =
                                          let uu____91762 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91762
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91760
                                         in
                                      [uu____91759]
                                    else []  in
                                  let query_prelude =
                                    let uu____91770 =
                                      let uu____91771 =
                                        let uu____91772 =
                                          let uu____91775 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91782 =
                                            let uu____91785 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91785
                                             in
                                          FStar_List.append uu____91775
                                            uu____91782
                                           in
                                        FStar_List.append env_decls
                                          uu____91772
                                         in
                                      FStar_All.pipe_right uu____91771
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91770
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91795 =
                                      let uu____91803 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91804 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91803,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91804)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91795
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
  