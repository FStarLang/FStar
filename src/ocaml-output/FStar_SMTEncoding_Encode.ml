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
  let uu____67893 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67893 with
  | (asym,a) ->
      let uu____67904 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67904 with
       | (xsym,x) ->
           let uu____67915 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67915 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____67993 =
                      let uu____68005 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____68005, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____67993  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68025 =
                      let uu____68033 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68033)  in
                    FStar_SMTEncoding_Util.mkApp uu____68025  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68052 =
                    let uu____68055 =
                      let uu____68058 =
                        let uu____68061 =
                          let uu____68062 =
                            let uu____68070 =
                              let uu____68071 =
                                let uu____68082 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68082)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68071
                               in
                            (uu____68070, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68062  in
                        let uu____68094 =
                          let uu____68097 =
                            let uu____68098 =
                              let uu____68106 =
                                let uu____68107 =
                                  let uu____68118 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68118)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68107
                                 in
                              (uu____68106,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68098  in
                          [uu____68097]  in
                        uu____68061 :: uu____68094  in
                      xtok_decl :: uu____68058  in
                    xname_decl :: uu____68055  in
                  (xtok1, (FStar_List.length vars), uu____68052)  in
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
                  let uu____68288 =
                    let uu____68309 =
                      let uu____68328 =
                        let uu____68329 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68329
                         in
                      quant axy uu____68328  in
                    (FStar_Parser_Const.op_Eq, uu____68309)  in
                  let uu____68346 =
                    let uu____68369 =
                      let uu____68390 =
                        let uu____68409 =
                          let uu____68410 =
                            let uu____68411 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68411  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68410
                           in
                        quant axy uu____68409  in
                      (FStar_Parser_Const.op_notEq, uu____68390)  in
                    let uu____68428 =
                      let uu____68451 =
                        let uu____68472 =
                          let uu____68491 =
                            let uu____68492 =
                              let uu____68493 =
                                let uu____68498 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68499 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68498, uu____68499)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68493  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68492
                             in
                          quant xy uu____68491  in
                        (FStar_Parser_Const.op_And, uu____68472)  in
                      let uu____68516 =
                        let uu____68539 =
                          let uu____68560 =
                            let uu____68579 =
                              let uu____68580 =
                                let uu____68581 =
                                  let uu____68586 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68587 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68586, uu____68587)  in
                                FStar_SMTEncoding_Util.mkOr uu____68581  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68580
                               in
                            quant xy uu____68579  in
                          (FStar_Parser_Const.op_Or, uu____68560)  in
                        let uu____68604 =
                          let uu____68627 =
                            let uu____68648 =
                              let uu____68667 =
                                let uu____68668 =
                                  let uu____68669 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68669
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68668
                                 in
                              quant qx uu____68667  in
                            (FStar_Parser_Const.op_Negation, uu____68648)  in
                          let uu____68686 =
                            let uu____68709 =
                              let uu____68730 =
                                let uu____68749 =
                                  let uu____68750 =
                                    let uu____68751 =
                                      let uu____68756 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68757 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68756, uu____68757)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68751
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68750
                                   in
                                quant xy uu____68749  in
                              (FStar_Parser_Const.op_LT, uu____68730)  in
                            let uu____68774 =
                              let uu____68797 =
                                let uu____68818 =
                                  let uu____68837 =
                                    let uu____68838 =
                                      let uu____68839 =
                                        let uu____68844 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68845 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68844, uu____68845)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68839
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68838
                                     in
                                  quant xy uu____68837  in
                                (FStar_Parser_Const.op_LTE, uu____68818)  in
                              let uu____68862 =
                                let uu____68885 =
                                  let uu____68906 =
                                    let uu____68925 =
                                      let uu____68926 =
                                        let uu____68927 =
                                          let uu____68932 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68933 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68932, uu____68933)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68927
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68926
                                       in
                                    quant xy uu____68925  in
                                  (FStar_Parser_Const.op_GT, uu____68906)  in
                                let uu____68950 =
                                  let uu____68973 =
                                    let uu____68994 =
                                      let uu____69013 =
                                        let uu____69014 =
                                          let uu____69015 =
                                            let uu____69020 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69021 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69020, uu____69021)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69015
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69014
                                         in
                                      quant xy uu____69013  in
                                    (FStar_Parser_Const.op_GTE, uu____68994)
                                     in
                                  let uu____69038 =
                                    let uu____69061 =
                                      let uu____69082 =
                                        let uu____69101 =
                                          let uu____69102 =
                                            let uu____69103 =
                                              let uu____69108 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69109 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69108, uu____69109)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69103
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69102
                                           in
                                        quant xy uu____69101  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69082)
                                       in
                                    let uu____69126 =
                                      let uu____69149 =
                                        let uu____69170 =
                                          let uu____69189 =
                                            let uu____69190 =
                                              let uu____69191 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69191
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69190
                                             in
                                          quant qx uu____69189  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69170)
                                         in
                                      let uu____69208 =
                                        let uu____69231 =
                                          let uu____69252 =
                                            let uu____69271 =
                                              let uu____69272 =
                                                let uu____69273 =
                                                  let uu____69278 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69279 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69278, uu____69279)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69273
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69272
                                               in
                                            quant xy uu____69271  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69252)
                                           in
                                        let uu____69296 =
                                          let uu____69319 =
                                            let uu____69340 =
                                              let uu____69359 =
                                                let uu____69360 =
                                                  let uu____69361 =
                                                    let uu____69366 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69367 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69366,
                                                      uu____69367)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69361
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69360
                                                 in
                                              quant xy uu____69359  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69340)
                                             in
                                          let uu____69384 =
                                            let uu____69407 =
                                              let uu____69428 =
                                                let uu____69447 =
                                                  let uu____69448 =
                                                    let uu____69449 =
                                                      let uu____69454 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69455 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69454,
                                                        uu____69455)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69449
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69448
                                                   in
                                                quant xy uu____69447  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69428)
                                               in
                                            let uu____69472 =
                                              let uu____69495 =
                                                let uu____69516 =
                                                  let uu____69535 =
                                                    let uu____69536 =
                                                      let uu____69537 =
                                                        let uu____69542 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69543 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69542,
                                                          uu____69543)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69537
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69536
                                                     in
                                                  quant xy uu____69535  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69516)
                                                 in
                                              let uu____69560 =
                                                let uu____69583 =
                                                  let uu____69604 =
                                                    let uu____69623 =
                                                      let uu____69624 =
                                                        let uu____69625 =
                                                          let uu____69630 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69631 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69630,
                                                            uu____69631)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69625
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69624
                                                       in
                                                    quant xy uu____69623  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69604)
                                                   in
                                                let uu____69648 =
                                                  let uu____69671 =
                                                    let uu____69692 =
                                                      let uu____69711 =
                                                        let uu____69712 =
                                                          let uu____69713 =
                                                            let uu____69718 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69719 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69718,
                                                              uu____69719)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69713
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69712
                                                         in
                                                      quant xy uu____69711
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69692)
                                                     in
                                                  let uu____69736 =
                                                    let uu____69759 =
                                                      let uu____69780 =
                                                        let uu____69799 =
                                                          let uu____69800 =
                                                            let uu____69801 =
                                                              let uu____69806
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69807
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69806,
                                                                uu____69807)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69801
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69800
                                                           in
                                                        quant xy uu____69799
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69780)
                                                       in
                                                    let uu____69824 =
                                                      let uu____69847 =
                                                        let uu____69868 =
                                                          let uu____69887 =
                                                            let uu____69888 =
                                                              let uu____69889
                                                                =
                                                                let uu____69894
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69895
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69894,
                                                                  uu____69895)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69889
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69888
                                                             in
                                                          quant xy
                                                            uu____69887
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69868)
                                                         in
                                                      let uu____69912 =
                                                        let uu____69935 =
                                                          let uu____69956 =
                                                            let uu____69975 =
                                                              let uu____69976
                                                                =
                                                                let uu____69977
                                                                  =
                                                                  let uu____69982
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____69983
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____69982,
                                                                    uu____69983)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____69977
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____69976
                                                               in
                                                            quant xy
                                                              uu____69975
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69956)
                                                           in
                                                        let uu____70000 =
                                                          let uu____70023 =
                                                            let uu____70044 =
                                                              let uu____70063
                                                                =
                                                                let uu____70064
                                                                  =
                                                                  let uu____70065
                                                                    =
                                                                    let uu____70070
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70071
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70070,
                                                                    uu____70071)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70065
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70064
                                                                 in
                                                              quant xy
                                                                uu____70063
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70044)
                                                             in
                                                          let uu____70088 =
                                                            let uu____70111 =
                                                              let uu____70132
                                                                =
                                                                let uu____70151
                                                                  =
                                                                  let uu____70152
                                                                    =
                                                                    let uu____70153
                                                                    =
                                                                    let uu____70158
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70159
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70158,
                                                                    uu____70159)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70153
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70152
                                                                   in
                                                                quant xy
                                                                  uu____70151
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70132)
                                                               in
                                                            let uu____70176 =
                                                              let uu____70199
                                                                =
                                                                let uu____70220
                                                                  =
                                                                  let uu____70239
                                                                    =
                                                                    let uu____70240
                                                                    =
                                                                    let uu____70241
                                                                    =
                                                                    let uu____70246
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70247
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70246,
                                                                    uu____70247)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70241
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70240
                                                                     in
                                                                  quant xy
                                                                    uu____70239
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70220)
                                                                 in
                                                              let uu____70264
                                                                =
                                                                let uu____70287
                                                                  =
                                                                  let uu____70308
                                                                    =
                                                                    let uu____70327
                                                                    =
                                                                    let uu____70328
                                                                    =
                                                                    let uu____70329
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70329
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70328
                                                                     in
                                                                    quant qx
                                                                    uu____70327
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70308)
                                                                   in
                                                                [uu____70287]
                                                                 in
                                                              uu____70199 ::
                                                                uu____70264
                                                               in
                                                            uu____70111 ::
                                                              uu____70176
                                                             in
                                                          uu____70023 ::
                                                            uu____70088
                                                           in
                                                        uu____69935 ::
                                                          uu____70000
                                                         in
                                                      uu____69847 ::
                                                        uu____69912
                                                       in
                                                    uu____69759 ::
                                                      uu____69824
                                                     in
                                                  uu____69671 :: uu____69736
                                                   in
                                                uu____69583 :: uu____69648
                                                 in
                                              uu____69495 :: uu____69560  in
                                            uu____69407 :: uu____69472  in
                                          uu____69319 :: uu____69384  in
                                        uu____69231 :: uu____69296  in
                                      uu____69149 :: uu____69208  in
                                    uu____69061 :: uu____69126  in
                                  uu____68973 :: uu____69038  in
                                uu____68885 :: uu____68950  in
                              uu____68797 :: uu____68862  in
                            uu____68709 :: uu____68774  in
                          uu____68627 :: uu____68686  in
                        uu____68539 :: uu____68604  in
                      uu____68451 :: uu____68516  in
                    uu____68369 :: uu____68428  in
                  uu____68288 :: uu____68346  in
                let mk1 l v1 =
                  let uu____70868 =
                    let uu____70880 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____70970  ->
                              match uu____70970 with
                              | (l',uu____70991) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70880
                      (FStar_Option.map
                         (fun uu____71090  ->
                            match uu____71090 with
                            | (uu____71118,b) ->
                                let uu____71152 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71152 v1))
                     in
                  FStar_All.pipe_right uu____70868 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71235  ->
                          match uu____71235 with
                          | (l',uu____71256) -> FStar_Ident.lid_equals l l'))
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
          let uu____71330 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71330 with
          | (xxsym,xx) ->
              let uu____71341 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71341 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71357 =
                     let uu____71365 =
                       let uu____71366 =
                         let uu____71377 =
                           let uu____71378 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71388 =
                             let uu____71399 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71399 :: vars  in
                           uu____71378 :: uu____71388  in
                         let uu____71425 =
                           let uu____71426 =
                             let uu____71431 =
                               let uu____71432 =
                                 let uu____71437 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71437)  in
                               FStar_SMTEncoding_Util.mkEq uu____71432  in
                             (xx_has_type, uu____71431)  in
                           FStar_SMTEncoding_Util.mkImp uu____71426  in
                         ([[xx_has_type]], uu____71377, uu____71425)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71366  in
                     let uu____71450 =
                       let uu____71452 =
                         let uu____71454 =
                           let uu____71456 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71456  in
                         Prims.op_Hat module_name uu____71454  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71452
                        in
                     (uu____71365,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71450)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71357)
  
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
    let uu____71512 =
      let uu____71514 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71514  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71512  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71536 =
      let uu____71537 =
        let uu____71545 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71545, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71537  in
    let uu____71550 =
      let uu____71553 =
        let uu____71554 =
          let uu____71562 =
            let uu____71563 =
              let uu____71574 =
                let uu____71575 =
                  let uu____71580 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71580)  in
                FStar_SMTEncoding_Util.mkImp uu____71575  in
              ([[typing_pred]], [xx], uu____71574)  in
            let uu____71605 =
              let uu____71620 = FStar_TypeChecker_Env.get_range env  in
              let uu____71621 = mkForall_fuel1 env  in
              uu____71621 uu____71620  in
            uu____71605 uu____71563  in
          (uu____71562, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71554  in
      [uu____71553]  in
    uu____71536 :: uu____71550  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71668 =
      let uu____71669 =
        let uu____71677 =
          let uu____71678 = FStar_TypeChecker_Env.get_range env  in
          let uu____71679 =
            let uu____71690 =
              let uu____71695 =
                let uu____71698 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71698]  in
              [uu____71695]  in
            let uu____71703 =
              let uu____71704 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71704 tt  in
            (uu____71690, [bb], uu____71703)  in
          FStar_SMTEncoding_Term.mkForall uu____71678 uu____71679  in
        (uu____71677, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71669  in
    let uu____71729 =
      let uu____71732 =
        let uu____71733 =
          let uu____71741 =
            let uu____71742 =
              let uu____71753 =
                let uu____71754 =
                  let uu____71759 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71759)  in
                FStar_SMTEncoding_Util.mkImp uu____71754  in
              ([[typing_pred]], [xx], uu____71753)  in
            let uu____71786 =
              let uu____71801 = FStar_TypeChecker_Env.get_range env  in
              let uu____71802 = mkForall_fuel1 env  in
              uu____71802 uu____71801  in
            uu____71786 uu____71742  in
          (uu____71741, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71733  in
      [uu____71732]  in
    uu____71668 :: uu____71729  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71845 =
        let uu____71846 =
          let uu____71852 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71852, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71846  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71845  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71866 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71866  in
    let uu____71871 =
      let uu____71872 =
        let uu____71880 =
          let uu____71881 = FStar_TypeChecker_Env.get_range env  in
          let uu____71882 =
            let uu____71893 =
              let uu____71898 =
                let uu____71901 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71901]  in
              [uu____71898]  in
            let uu____71906 =
              let uu____71907 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71907 tt  in
            (uu____71893, [bb], uu____71906)  in
          FStar_SMTEncoding_Term.mkForall uu____71881 uu____71882  in
        (uu____71880, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71872  in
    let uu____71932 =
      let uu____71935 =
        let uu____71936 =
          let uu____71944 =
            let uu____71945 =
              let uu____71956 =
                let uu____71957 =
                  let uu____71962 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71962)  in
                FStar_SMTEncoding_Util.mkImp uu____71957  in
              ([[typing_pred]], [xx], uu____71956)  in
            let uu____71989 =
              let uu____72004 = FStar_TypeChecker_Env.get_range env  in
              let uu____72005 = mkForall_fuel1 env  in
              uu____72005 uu____72004  in
            uu____71989 uu____71945  in
          (uu____71944, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71936  in
      let uu____72027 =
        let uu____72030 =
          let uu____72031 =
            let uu____72039 =
              let uu____72040 =
                let uu____72051 =
                  let uu____72052 =
                    let uu____72057 =
                      let uu____72058 =
                        let uu____72061 =
                          let uu____72064 =
                            let uu____72067 =
                              let uu____72068 =
                                let uu____72073 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72074 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72073, uu____72074)  in
                              FStar_SMTEncoding_Util.mkGT uu____72068  in
                            let uu____72076 =
                              let uu____72079 =
                                let uu____72080 =
                                  let uu____72085 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72086 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72085, uu____72086)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72080  in
                              let uu____72088 =
                                let uu____72091 =
                                  let uu____72092 =
                                    let uu____72097 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72098 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72097, uu____72098)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72092  in
                                [uu____72091]  in
                              uu____72079 :: uu____72088  in
                            uu____72067 :: uu____72076  in
                          typing_pred_y :: uu____72064  in
                        typing_pred :: uu____72061  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72058  in
                    (uu____72057, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72052  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72051)
                 in
              let uu____72131 =
                let uu____72146 = FStar_TypeChecker_Env.get_range env  in
                let uu____72147 = mkForall_fuel1 env  in
                uu____72147 uu____72146  in
              uu____72131 uu____72040  in
            (uu____72039,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72031  in
        [uu____72030]  in
      uu____71935 :: uu____72027  in
    uu____71871 :: uu____71932  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72190 =
        let uu____72191 =
          let uu____72197 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72197, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72191  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72190  in
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
      let uu____72213 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72213  in
    let uu____72218 =
      let uu____72219 =
        let uu____72227 =
          let uu____72228 = FStar_TypeChecker_Env.get_range env  in
          let uu____72229 =
            let uu____72240 =
              let uu____72245 =
                let uu____72248 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72248]  in
              [uu____72245]  in
            let uu____72253 =
              let uu____72254 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72254 tt  in
            (uu____72240, [bb], uu____72253)  in
          FStar_SMTEncoding_Term.mkForall uu____72228 uu____72229  in
        (uu____72227, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72219  in
    let uu____72279 =
      let uu____72282 =
        let uu____72283 =
          let uu____72291 =
            let uu____72292 =
              let uu____72303 =
                let uu____72304 =
                  let uu____72309 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72309)  in
                FStar_SMTEncoding_Util.mkImp uu____72304  in
              ([[typing_pred]], [xx], uu____72303)  in
            let uu____72336 =
              let uu____72351 = FStar_TypeChecker_Env.get_range env  in
              let uu____72352 = mkForall_fuel1 env  in
              uu____72352 uu____72351  in
            uu____72336 uu____72292  in
          (uu____72291, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72283  in
      let uu____72374 =
        let uu____72377 =
          let uu____72378 =
            let uu____72386 =
              let uu____72387 =
                let uu____72398 =
                  let uu____72399 =
                    let uu____72404 =
                      let uu____72405 =
                        let uu____72408 =
                          let uu____72411 =
                            let uu____72414 =
                              let uu____72415 =
                                let uu____72420 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72421 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72420, uu____72421)  in
                              FStar_SMTEncoding_Util.mkGT uu____72415  in
                            let uu____72423 =
                              let uu____72426 =
                                let uu____72427 =
                                  let uu____72432 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72433 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72432, uu____72433)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72427  in
                              let uu____72435 =
                                let uu____72438 =
                                  let uu____72439 =
                                    let uu____72444 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72445 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72444, uu____72445)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72439  in
                                [uu____72438]  in
                              uu____72426 :: uu____72435  in
                            uu____72414 :: uu____72423  in
                          typing_pred_y :: uu____72411  in
                        typing_pred :: uu____72408  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72405  in
                    (uu____72404, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72399  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72398)
                 in
              let uu____72478 =
                let uu____72493 = FStar_TypeChecker_Env.get_range env  in
                let uu____72494 = mkForall_fuel1 env  in
                uu____72494 uu____72493  in
              uu____72478 uu____72387  in
            (uu____72386,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72378  in
        [uu____72377]  in
      uu____72282 :: uu____72374  in
    uu____72218 :: uu____72279  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72541 =
      let uu____72542 =
        let uu____72550 =
          let uu____72551 = FStar_TypeChecker_Env.get_range env  in
          let uu____72552 =
            let uu____72563 =
              let uu____72568 =
                let uu____72571 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72571]  in
              [uu____72568]  in
            let uu____72576 =
              let uu____72577 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72577 tt  in
            (uu____72563, [bb], uu____72576)  in
          FStar_SMTEncoding_Term.mkForall uu____72551 uu____72552  in
        (uu____72550, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72542  in
    let uu____72602 =
      let uu____72605 =
        let uu____72606 =
          let uu____72614 =
            let uu____72615 =
              let uu____72626 =
                let uu____72627 =
                  let uu____72632 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72632)  in
                FStar_SMTEncoding_Util.mkImp uu____72627  in
              ([[typing_pred]], [xx], uu____72626)  in
            let uu____72659 =
              let uu____72674 = FStar_TypeChecker_Env.get_range env  in
              let uu____72675 = mkForall_fuel1 env  in
              uu____72675 uu____72674  in
            uu____72659 uu____72615  in
          (uu____72614, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72606  in
      [uu____72605]  in
    uu____72541 :: uu____72602  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72722 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72722]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72752 =
      let uu____72753 =
        let uu____72761 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72761, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72753  in
    [uu____72752]  in
  let mk_and_interp env conj uu____72784 =
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
    let uu____72813 =
      let uu____72814 =
        let uu____72822 =
          let uu____72823 = FStar_TypeChecker_Env.get_range env  in
          let uu____72824 =
            let uu____72835 =
              let uu____72836 =
                let uu____72841 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72841, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72836  in
            ([[l_and_a_b]], [aa; bb], uu____72835)  in
          FStar_SMTEncoding_Term.mkForall uu____72823 uu____72824  in
        (uu____72822, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72814  in
    [uu____72813]  in
  let mk_or_interp env disj uu____72896 =
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
    let uu____72925 =
      let uu____72926 =
        let uu____72934 =
          let uu____72935 = FStar_TypeChecker_Env.get_range env  in
          let uu____72936 =
            let uu____72947 =
              let uu____72948 =
                let uu____72953 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72953, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72948  in
            ([[l_or_a_b]], [aa; bb], uu____72947)  in
          FStar_SMTEncoding_Term.mkForall uu____72935 uu____72936  in
        (uu____72934, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72926  in
    [uu____72925]  in
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
    let uu____73031 =
      let uu____73032 =
        let uu____73040 =
          let uu____73041 = FStar_TypeChecker_Env.get_range env  in
          let uu____73042 =
            let uu____73053 =
              let uu____73054 =
                let uu____73059 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73059, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73054  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73053)  in
          FStar_SMTEncoding_Term.mkForall uu____73041 uu____73042  in
        (uu____73040, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73032  in
    [uu____73031]  in
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
    let uu____73149 =
      let uu____73150 =
        let uu____73158 =
          let uu____73159 = FStar_TypeChecker_Env.get_range env  in
          let uu____73160 =
            let uu____73171 =
              let uu____73172 =
                let uu____73177 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73177, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73172  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73171)  in
          FStar_SMTEncoding_Term.mkForall uu____73159 uu____73160  in
        (uu____73158, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73150  in
    [uu____73149]  in
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
    let uu____73277 =
      let uu____73278 =
        let uu____73286 =
          let uu____73287 = FStar_TypeChecker_Env.get_range env  in
          let uu____73288 =
            let uu____73299 =
              let uu____73300 =
                let uu____73305 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73305, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73300  in
            ([[l_imp_a_b]], [aa; bb], uu____73299)  in
          FStar_SMTEncoding_Term.mkForall uu____73287 uu____73288  in
        (uu____73286, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73278  in
    [uu____73277]  in
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
    let uu____73389 =
      let uu____73390 =
        let uu____73398 =
          let uu____73399 = FStar_TypeChecker_Env.get_range env  in
          let uu____73400 =
            let uu____73411 =
              let uu____73412 =
                let uu____73417 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73417, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73412  in
            ([[l_iff_a_b]], [aa; bb], uu____73411)  in
          FStar_SMTEncoding_Term.mkForall uu____73399 uu____73400  in
        (uu____73398, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73390  in
    [uu____73389]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73488 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73488  in
    let uu____73493 =
      let uu____73494 =
        let uu____73502 =
          let uu____73503 = FStar_TypeChecker_Env.get_range env  in
          let uu____73504 =
            let uu____73515 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73515)  in
          FStar_SMTEncoding_Term.mkForall uu____73503 uu____73504  in
        (uu____73502, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73494  in
    [uu____73493]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73568 =
      let uu____73569 =
        let uu____73577 =
          let uu____73578 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73578 range_ty  in
        let uu____73579 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73577, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73579)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73569  in
    [uu____73568]  in
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
        let uu____73625 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73625 x1 t  in
      let uu____73627 = FStar_TypeChecker_Env.get_range env  in
      let uu____73628 =
        let uu____73639 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73639)  in
      FStar_SMTEncoding_Term.mkForall uu____73627 uu____73628  in
    let uu____73664 =
      let uu____73665 =
        let uu____73673 =
          let uu____73674 = FStar_TypeChecker_Env.get_range env  in
          let uu____73675 =
            let uu____73686 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73686)  in
          FStar_SMTEncoding_Term.mkForall uu____73674 uu____73675  in
        (uu____73673,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73665  in
    [uu____73664]  in
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
    let uu____73747 =
      let uu____73748 =
        let uu____73756 =
          let uu____73757 = FStar_TypeChecker_Env.get_range env  in
          let uu____73758 =
            let uu____73774 =
              let uu____73775 =
                let uu____73780 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73781 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73780, uu____73781)  in
              FStar_SMTEncoding_Util.mkAnd uu____73775  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73774)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73757 uu____73758  in
        (uu____73756,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73748  in
    [uu____73747]  in
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
          let uu____74339 =
            FStar_Util.find_opt
              (fun uu____74377  ->
                 match uu____74377 with
                 | (l,uu____74393) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74339 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74436,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74497 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74497 with
        | (form,decls) ->
            let uu____74506 =
              let uu____74509 =
                let uu____74512 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74512]  in
              FStar_All.pipe_right uu____74509
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74506
  
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
              let uu____74571 =
                ((let uu____74575 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74575) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74571
              then
                let arg_sorts =
                  let uu____74587 =
                    let uu____74588 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74588.FStar_Syntax_Syntax.n  in
                  match uu____74587 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74594) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74632  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74639 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74641 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74641 with
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
                    let uu____74673 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74673, env1)
              else
                (let uu____74678 = prims.is lid  in
                 if uu____74678
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74687 = prims.mk lid vname  in
                   match uu____74687 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74711 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74711, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74720 =
                      let uu____74739 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74739 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74767 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74767
                            then
                              let uu____74772 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_74775 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_74775.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_74775.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_74775.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_74775.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_74775.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_74775.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_74775.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_74775.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_74775.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_74775.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_74775.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_74775.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_74775.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_74775.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_74775.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_74775.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_74775.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_74775.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_74775.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_74775.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_74775.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_74775.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_74775.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_74775.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_74775.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_74775.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_74775.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_74775.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_74775.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_74775.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_74775.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_74775.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_74775.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_74775.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_74775.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_74775.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_74775.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_74775.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_74775.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_74775.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_74775.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_74775.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74772
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74798 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74798)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74720 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74904  ->
                                  match uu___639_74904 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74908 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74908 with
                                       | (uu____74941,xxv) ->
                                           let xx =
                                             let uu____74980 =
                                               let uu____74981 =
                                                 let uu____74987 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____74987,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____74981
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____74980
                                              in
                                           let uu____74990 =
                                             let uu____74991 =
                                               let uu____74999 =
                                                 let uu____75000 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75001 =
                                                   let uu____75012 =
                                                     let uu____75013 =
                                                       let uu____75018 =
                                                         let uu____75019 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75019
                                                          in
                                                       (vapp, uu____75018)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75013
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75012)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75000 uu____75001
                                                  in
                                               (uu____74999,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____74991
                                              in
                                           [uu____74990])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75034 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75034 with
                                       | (uu____75067,xxv) ->
                                           let xx =
                                             let uu____75106 =
                                               let uu____75107 =
                                                 let uu____75113 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75113,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75107
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75106
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
                                           let uu____75124 =
                                             let uu____75125 =
                                               let uu____75133 =
                                                 let uu____75134 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75135 =
                                                   let uu____75146 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75146)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75134 uu____75135
                                                  in
                                               (uu____75133,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75125
                                              in
                                           [uu____75124])
                                  | uu____75159 -> []))
                           in
                        let uu____75160 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75160 with
                         | (vars,guards,env',decls1,uu____75185) ->
                             let uu____75198 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75211 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75211, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75215 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75215 with
                                    | (g,ds) ->
                                        let uu____75228 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75228,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75198 with
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
                                  let should_thunk uu____75251 =
                                    let is_type1 t =
                                      let uu____75259 =
                                        let uu____75260 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75260.FStar_Syntax_Syntax.n  in
                                      match uu____75259 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75264 -> true
                                      | uu____75266 -> false  in
                                    let is_squash1 t =
                                      let uu____75275 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75275 with
                                      | (head1,uu____75294) ->
                                          let uu____75319 =
                                            let uu____75320 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75320.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75319 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75325;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75326;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75328;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75329;_};_},uu____75330)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75338 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75343 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75343))
                                       &&
                                       (let uu____75349 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75349))
                                      &&
                                      (let uu____75352 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75352)
                                     in
                                  let uu____75354 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75413 -> (false, vars)  in
                                  (match uu____75354 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75463 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75463 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75495 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75504 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75504
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75515 ->
                                                  let uu____75524 =
                                                    let uu____75532 =
                                                      get_vtok ()  in
                                                    (uu____75532, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75524
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75539 =
                                                let uu____75547 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75547)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75539
                                               in
                                            let uu____75561 =
                                              let vname_decl =
                                                let uu____75569 =
                                                  let uu____75581 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75581,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75569
                                                 in
                                              let uu____75592 =
                                                let env2 =
                                                  let uu___1026_75598 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_75598.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75599 =
                                                  let uu____75601 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75601
                                                   in
                                                if uu____75599
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75592 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75618 =
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
                                                        let uu____75644 =
                                                          let uu____75647 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75647
                                                           in
                                                        let uu____75654 =
                                                          let uu____75655 =
                                                            let uu____75658 =
                                                              let uu____75659
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75659
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75663  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75663)
                                                              uu____75658
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75655
                                                           in
                                                        (uu____75644,
                                                          uu____75654)
                                                    | uu____75666 when
                                                        thunked ->
                                                        let uu____75677 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75677
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75692
                                                                 =
                                                                 let uu____75700
                                                                   =
                                                                   let uu____75703
                                                                    =
                                                                    let uu____75706
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75706]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75703
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75700)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75692
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75714
                                                               =
                                                               let uu____75722
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75722,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75714
                                                              in
                                                           let uu____75727 =
                                                             let uu____75730
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75730
                                                              in
                                                           (uu____75727,
                                                             env1))
                                                    | uu____75739 ->
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
                                                          let uu____75763 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75764 =
                                                            let uu____75775 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75775)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75763
                                                            uu____75764
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75785 =
                                                            let uu____75793 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75793,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75785
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
                                                            let uu____75804 =
                                                              let uu____75805
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75805]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75804
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75832 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75833 =
                                                              let uu____75844
                                                                =
                                                                let uu____75845
                                                                  =
                                                                  let uu____75850
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75851
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75850,
                                                                    uu____75851)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75845
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75844)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75832
                                                              uu____75833
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75880 =
                                                          let uu____75883 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75883
                                                           in
                                                        (uu____75880, env1)
                                                     in
                                                  (match uu____75618 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75904 =
                                                         let uu____75907 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75907
                                                           tok_decl
                                                          in
                                                       (uu____75904, env2))
                                               in
                                            (match uu____75561 with
                                             | (decls2,env2) ->
                                                 let uu____75926 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75936 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75936 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75951 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75951, decls)
                                                    in
                                                 (match uu____75926 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____75966 =
                                                          let uu____75974 =
                                                            let uu____75975 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75976 =
                                                              let uu____75987
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____75987)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75975
                                                              uu____75976
                                                             in
                                                          (uu____75974,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____75966
                                                         in
                                                      let freshness =
                                                        let uu____76003 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____76003
                                                        then
                                                          let uu____76011 =
                                                            let uu____76012 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76013 =
                                                              let uu____76026
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76033
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76026,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76033)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____76012
                                                              uu____76013
                                                             in
                                                          let uu____76039 =
                                                            let uu____76042 =
                                                              let uu____76043
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76043
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76042]  in
                                                          uu____76011 ::
                                                            uu____76039
                                                        else []  in
                                                      let g =
                                                        let uu____76049 =
                                                          let uu____76052 =
                                                            let uu____76055 =
                                                              let uu____76058
                                                                =
                                                                let uu____76061
                                                                  =
                                                                  let uu____76064
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76064
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76061
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76058
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76055
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76052
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76049
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
          let uu____76104 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76104 with
          | FStar_Pervasives_Native.None  ->
              let uu____76115 = encode_free_var false env x t t_norm []  in
              (match uu____76115 with
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
            let uu____76178 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76178 with
            | (decls,env1) ->
                let uu____76189 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76189
                then
                  let uu____76196 =
                    let uu____76197 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76197  in
                  (uu____76196, env1)
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
             (fun uu____76253  ->
                fun lb  ->
                  match uu____76253 with
                  | (decls,env1) ->
                      let uu____76273 =
                        let uu____76278 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76278
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76273 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76307 = FStar_Syntax_Util.head_and_args t  in
    match uu____76307 with
    | (hd1,args) ->
        let uu____76351 =
          let uu____76352 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76352.FStar_Syntax_Syntax.n  in
        (match uu____76351 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76358,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76382 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76393 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_76401 = en  in
    let uu____76402 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_76401.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_76401.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_76401.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_76401.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_76401.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_76401.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_76401.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_76401.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_76401.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_76401.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76402
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76432  ->
      fun quals  ->
        match uu____76432 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76537 = FStar_Util.first_N nbinders formals  in
              match uu____76537 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76634  ->
                         fun uu____76635  ->
                           match (uu____76634, uu____76635) with
                           | ((formal,uu____76661),(binder,uu____76663)) ->
                               let uu____76684 =
                                 let uu____76691 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76691)  in
                               FStar_Syntax_Syntax.NT uu____76684) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76705 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76746  ->
                              match uu____76746 with
                              | (x,i) ->
                                  let uu____76765 =
                                    let uu___1139_76766 = x  in
                                    let uu____76767 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_76766.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_76766.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76767
                                    }  in
                                  (uu____76765, i)))
                       in
                    FStar_All.pipe_right uu____76705
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76791 =
                      let uu____76796 = FStar_Syntax_Subst.compress body  in
                      let uu____76797 =
                        let uu____76798 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76798
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76796
                        uu____76797
                       in
                    uu____76791 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_76847 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_76847.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_76847.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_76847.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_76847.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_76847.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_76847.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_76847.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_76847.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_76847.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_76847.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_76847.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_76847.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_76847.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_76847.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_76847.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_76847.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_76847.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_76847.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_76847.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_76847.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_76847.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_76847.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_76847.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_76847.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_76847.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_76847.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_76847.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_76847.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_76847.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_76847.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_76847.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_76847.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_76847.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_76847.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_76847.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_76847.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_76847.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_76847.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_76847.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_76847.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_76847.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_76847.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76919  ->
                       fun uu____76920  ->
                         match (uu____76919, uu____76920) with
                         | ((x,uu____76946),(b,uu____76948)) ->
                             let uu____76969 =
                               let uu____76976 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____76976)  in
                             FStar_Syntax_Syntax.NT uu____76969) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____77001 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____77001
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77030 ->
                    let uu____77037 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77037
                | uu____77038 when Prims.op_Negation norm1 ->
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
                | uu____77041 ->
                    let uu____77042 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77042)
                 in
              let aux t1 e1 =
                let uu____77084 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77084 with
                | (binders,body,lopt) ->
                    let uu____77116 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77132 -> arrow_formals_comp_norm false t1  in
                    (match uu____77116 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77166 =
                           if nformals < nbinders
                           then
                             let uu____77200 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77200 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77280 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77280)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77310 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77310 with
                                | (binders1,body1) ->
                                    let uu____77363 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77363))
                             else
                               (let uu____77376 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77376))
                            in
                         (match uu____77166 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77436 = aux t e  in
              match uu____77436 with
              | (binders,body,comp) ->
                  let uu____77482 =
                    let uu____77493 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77493
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77508 = aux comp1 body1  in
                      match uu____77508 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77482 with
                   | (binders1,body1,comp1) ->
                       let uu____77591 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77591, comp1))
               in
            (try
               (fun uu___1216_77618  ->
                  match () with
                  | () ->
                      let uu____77625 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77625
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77641 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77704  ->
                                   fun lb  ->
                                     match uu____77704 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77759 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77759
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77765 =
                                             let uu____77774 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77774
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77765 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77641 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77915;
                                    FStar_Syntax_Syntax.lbeff = uu____77916;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77918;
                                    FStar_Syntax_Syntax.lbpos = uu____77919;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77943 =
                                     let uu____77950 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77950 with
                                     | (tcenv',uu____77966,e_t) ->
                                         let uu____77972 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____77983 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____77972 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_78000 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_78000.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77943 with
                                    | (env',e1,t_norm1) ->
                                        let uu____78010 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____78010 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78030 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78030
                                               then
                                                 let uu____78035 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78038 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78035 uu____78038
                                               else ());
                                              (let uu____78043 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78043 with
                                               | (vars,_guards,env'1,binder_decls,uu____78070)
                                                   ->
                                                   let uu____78083 =
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
                                                         let uu____78100 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78100
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78122 =
                                                          let uu____78123 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78124 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78123 fvb
                                                            uu____78124
                                                           in
                                                        (vars, uu____78122))
                                                      in
                                                   (match uu____78083 with
                                                    | (vars1,app) ->
                                                        let uu____78135 =
                                                          let is_logical =
                                                            let uu____78148 =
                                                              let uu____78149
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78149.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78148
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78155 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78159 =
                                                              let uu____78160
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78160
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78159
                                                              (fun lid  ->
                                                                 let uu____78169
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78169
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78170 =
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
                                                          if uu____78170
                                                          then
                                                            let uu____78186 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78187 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78186,
                                                              uu____78187)
                                                          else
                                                            (let uu____78198
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78198))
                                                           in
                                                        (match uu____78135
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78222
                                                                 =
                                                                 let uu____78230
                                                                   =
                                                                   let uu____78231
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78232
                                                                    =
                                                                    let uu____78243
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78243)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78231
                                                                    uu____78232
                                                                    in
                                                                 let uu____78252
                                                                   =
                                                                   let uu____78253
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78253
                                                                    in
                                                                 (uu____78230,
                                                                   uu____78252,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78222
                                                                in
                                                             let uu____78259
                                                               =
                                                               let uu____78262
                                                                 =
                                                                 let uu____78265
                                                                   =
                                                                   let uu____78268
                                                                    =
                                                                    let uu____78271
                                                                    =
                                                                    let uu____78274
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78274
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78271
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78268
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78265
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78262
                                                                in
                                                             (uu____78259,
                                                               env2)))))))
                               | uu____78283 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78343 =
                                   let uu____78349 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78349,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78343  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78355 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78408  ->
                                         fun fvb  ->
                                           match uu____78408 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78463 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78463
                                                  in
                                               let gtok =
                                                 let uu____78467 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78467
                                                  in
                                               let env4 =
                                                 let uu____78470 =
                                                   let uu____78473 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78479  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78479) uu____78473
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78470
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78355 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78599
                                     t_norm uu____78601 =
                                     match (uu____78599, uu____78601) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78631;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78632;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78634;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78635;_})
                                         ->
                                         let uu____78662 =
                                           let uu____78669 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78669 with
                                           | (tcenv',uu____78685,e_t) ->
                                               let uu____78691 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78702 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78691 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_78719 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_78719.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78662 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78732 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78732
                                                then
                                                  let uu____78737 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78739 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78741 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78737 uu____78739
                                                    uu____78741
                                                else ());
                                               (let uu____78746 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78746 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78773 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78773 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78795 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78795
                                                           then
                                                             let uu____78800
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78802
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78805
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78807
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78800
                                                               uu____78802
                                                               uu____78805
                                                               uu____78807
                                                           else ());
                                                          (let uu____78812 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78812
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78841)
                                                               ->
                                                               let uu____78854
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78867,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78871
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78871
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78884
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78884,
                                                                    decls0))
                                                                  in
                                                               (match uu____78854
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
                                                                    let uu____78905
                                                                    =
                                                                    let uu____78917
                                                                    =
                                                                    let uu____78920
                                                                    =
                                                                    let uu____78923
                                                                    =
                                                                    let uu____78926
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78926
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78923
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78920
                                                                     in
                                                                    (g,
                                                                    uu____78917,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78905
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
                                                                    let uu____78956
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78956
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
                                                                    let uu____78971
                                                                    =
                                                                    let uu____78974
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____78974
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78971
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____78980
                                                                    =
                                                                    let uu____78983
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____78983
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78980
                                                                     in
                                                                    let uu____78988
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____78988
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____79004
                                                                    =
                                                                    let uu____79012
                                                                    =
                                                                    let uu____79013
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79014
                                                                    =
                                                                    let uu____79030
                                                                    =
                                                                    let uu____79031
                                                                    =
                                                                    let uu____79036
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79036)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79031
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79030)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79013
                                                                    uu____79014
                                                                     in
                                                                    let uu____79050
                                                                    =
                                                                    let uu____79051
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79051
                                                                     in
                                                                    (uu____79012,
                                                                    uu____79050,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79004
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79058
                                                                    =
                                                                    let uu____79066
                                                                    =
                                                                    let uu____79067
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79068
                                                                    =
                                                                    let uu____79079
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79079)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79067
                                                                    uu____79068
                                                                     in
                                                                    (uu____79066,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79058
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79093
                                                                    =
                                                                    let uu____79101
                                                                    =
                                                                    let uu____79102
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79103
                                                                    =
                                                                    let uu____79114
                                                                    =
                                                                    let uu____79115
                                                                    =
                                                                    let uu____79120
                                                                    =
                                                                    let uu____79121
                                                                    =
                                                                    let uu____79124
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79124
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79121
                                                                     in
                                                                    (gsapp,
                                                                    uu____79120)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79115
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79114)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79102
                                                                    uu____79103
                                                                     in
                                                                    (uu____79101,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79093
                                                                     in
                                                                    let uu____79138
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
                                                                    let uu____79150
                                                                    =
                                                                    let uu____79151
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79151
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79150
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79153
                                                                    =
                                                                    let uu____79161
                                                                    =
                                                                    let uu____79162
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79163
                                                                    =
                                                                    let uu____79174
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79174)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79162
                                                                    uu____79163
                                                                     in
                                                                    (uu____79161,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79153
                                                                     in
                                                                    let uu____79187
                                                                    =
                                                                    let uu____79196
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79196
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79211
                                                                    =
                                                                    let uu____79214
                                                                    =
                                                                    let uu____79215
                                                                    =
                                                                    let uu____79223
                                                                    =
                                                                    let uu____79224
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79225
                                                                    =
                                                                    let uu____79236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79236)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79224
                                                                    uu____79225
                                                                     in
                                                                    (uu____79223,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79215
                                                                     in
                                                                    [uu____79214]
                                                                     in
                                                                    (d3,
                                                                    uu____79211)
                                                                     in
                                                                    match uu____79187
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79138
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79293
                                                                    =
                                                                    let uu____79296
                                                                    =
                                                                    let uu____79299
                                                                    =
                                                                    let uu____79302
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79302
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79299
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79296
                                                                     in
                                                                    let uu____79309
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79293,
                                                                    uu____79309,
                                                                    env02))))))))))
                                      in
                                   let uu____79314 =
                                     let uu____79327 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79390  ->
                                          fun uu____79391  ->
                                            match (uu____79390, uu____79391)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79516 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79516 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79327
                                      in
                                   (match uu____79314 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79583 =
                                          let isDeclFun uu___640_79600 =
                                            match uu___640_79600 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79602 -> true
                                            | uu____79615 -> false  in
                                          let uu____79617 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79617
                                            (fun decls3  ->
                                               let uu____79647 =
                                                 FStar_List.fold_left
                                                   (fun uu____79678  ->
                                                      fun elt  ->
                                                        match uu____79678
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79719 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79719
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79747
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79747
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
                                                                    let uu___1459_79785
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_79785.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_79785.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_79785.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79647 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79817 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79817, elts, rest))
                                           in
                                        (match uu____79583 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79846 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79852  ->
                                        match uu___641_79852 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79855 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79863 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79863)))
                                in
                             if uu____79846
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_79885  ->
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
                   let uu____79924 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79924
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79943 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79943, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____79999 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____79999 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____80005 = encode_sigelt' env se  in
      match uu____80005 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80017 =
                  let uu____80020 =
                    let uu____80021 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80021  in
                  [uu____80020]  in
                FStar_All.pipe_right uu____80017
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80026 ->
                let uu____80027 =
                  let uu____80030 =
                    let uu____80033 =
                      let uu____80034 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80034  in
                    [uu____80033]  in
                  FStar_All.pipe_right uu____80030
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80041 =
                  let uu____80044 =
                    let uu____80047 =
                      let uu____80050 =
                        let uu____80051 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80051  in
                      [uu____80050]  in
                    FStar_All.pipe_right uu____80047
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80044  in
                FStar_List.append uu____80027 uu____80041
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80065 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80065
       then
         let uu____80070 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80070
       else ());
      (let is_opaque_to_smt t =
         let uu____80082 =
           let uu____80083 = FStar_Syntax_Subst.compress t  in
           uu____80083.FStar_Syntax_Syntax.n  in
         match uu____80082 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80088)) -> s = "opaque_to_smt"
         | uu____80093 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80102 =
           let uu____80103 = FStar_Syntax_Subst.compress t  in
           uu____80103.FStar_Syntax_Syntax.n  in
         match uu____80102 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80108)) -> s = "uninterpreted_by_smt"
         | uu____80113 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80119 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80125 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80137 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80138 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80139 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80152 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80154 =
             let uu____80156 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80156  in
           if uu____80154
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80185 ->
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
                let uu____80217 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80217 with
                | (formals,uu____80237) ->
                    let arity = FStar_List.length formals  in
                    let uu____80261 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80261 with
                     | (aname,atok,env2) ->
                         let uu____80283 =
                           let uu____80288 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____80288 env2
                            in
                         (match uu____80283 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80300 =
                                  let uu____80301 =
                                    let uu____80313 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80333  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80313,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80301
                                   in
                                [uu____80300;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80350 =
                                let aux uu____80396 uu____80397 =
                                  match (uu____80396, uu____80397) with
                                  | ((bv,uu____80441),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80473 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80473 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80496 =
                                             let uu____80499 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80499 :: acc_sorts  in
                                           (env4, uu____80496, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80350 with
                               | (uu____80531,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80547 =
                                       let uu____80555 =
                                         let uu____80556 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80557 =
                                           let uu____80568 =
                                             let uu____80569 =
                                               let uu____80574 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80574)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80569
                                              in
                                           ([[app]], xs_sorts, uu____80568)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80556 uu____80557
                                          in
                                       (uu____80555,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80547
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80589 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80589
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80592 =
                                       let uu____80600 =
                                         let uu____80601 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80602 =
                                           let uu____80613 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80613)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80601 uu____80602
                                          in
                                       (uu____80600,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80592
                                      in
                                   let uu____80626 =
                                     let uu____80629 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80629  in
                                   (env2, uu____80626))))
                 in
              let uu____80638 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80638 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80664,uu____80665)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80666 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80666 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80688,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80695 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80701  ->
                       match uu___642_80701 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80704 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80710 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80713 -> false))
                in
             Prims.op_Negation uu____80695  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80723 =
                let uu____80728 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80728 env fv t quals  in
              match uu____80723 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80742 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80742  in
                  let uu____80745 =
                    let uu____80746 =
                      let uu____80749 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80749
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80746  in
                  (uu____80745, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80759 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80759 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_80771 = env  in
                  let uu____80772 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_80771.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_80771.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_80771.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80772;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_80771.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_80771.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_80771.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_80771.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_80771.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_80771.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_80771.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____80774 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80774 with
                 | (f3,decls) ->
                     let g =
                       let uu____80788 =
                         let uu____80791 =
                           let uu____80792 =
                             let uu____80800 =
                               let uu____80801 =
                                 let uu____80803 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80803
                                  in
                               FStar_Pervasives_Native.Some uu____80801  in
                             let uu____80807 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80800, uu____80807)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80792  in
                         [uu____80791]  in
                       FStar_All.pipe_right uu____80788
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80816) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80830 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80852 =
                        let uu____80855 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80855.FStar_Syntax_Syntax.fv_name  in
                      uu____80852.FStar_Syntax_Syntax.v  in
                    let uu____80856 =
                      let uu____80858 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80858  in
                    if uu____80856
                    then
                      let val_decl =
                        let uu___1629_80890 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_80890.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_80890.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_80890.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80891 = encode_sigelt' env1 val_decl  in
                      match uu____80891 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80830 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80927,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80929;
                           FStar_Syntax_Syntax.lbtyp = uu____80930;
                           FStar_Syntax_Syntax.lbeff = uu____80931;
                           FStar_Syntax_Syntax.lbdef = uu____80932;
                           FStar_Syntax_Syntax.lbattrs = uu____80933;
                           FStar_Syntax_Syntax.lbpos = uu____80934;_}::[]),uu____80935)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80954 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80954 with
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
                  let uu____80992 =
                    let uu____80995 =
                      let uu____80996 =
                        let uu____81004 =
                          let uu____81005 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____81006 =
                            let uu____81017 =
                              let uu____81018 =
                                let uu____81023 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81023)  in
                              FStar_SMTEncoding_Util.mkEq uu____81018  in
                            ([[b2t_x]], [xx], uu____81017)  in
                          FStar_SMTEncoding_Term.mkForall uu____81005
                            uu____81006
                           in
                        (uu____81004,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____80996  in
                    [uu____80995]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____80992
                   in
                let uu____81061 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81061, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81064,uu____81065) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81075  ->
                   match uu___643_81075 with
                   | FStar_Syntax_Syntax.Discriminator uu____81077 -> true
                   | uu____81079 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81081,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81093 =
                      let uu____81095 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81095.FStar_Ident.idText  in
                    uu____81093 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81102  ->
                      match uu___644_81102 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81105 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81108) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81122  ->
                   match uu___645_81122 with
                   | FStar_Syntax_Syntax.Projector uu____81124 -> true
                   | uu____81130 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81134 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81134 with
            | FStar_Pervasives_Native.Some uu____81141 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_81143 = se  in
                  let uu____81144 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81144;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_81143.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_81143.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_81143.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81147) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81162) ->
           let uu____81171 = encode_sigelts env ses  in
           (match uu____81171 with
            | (g,env1) ->
                let uu____81182 =
                  FStar_List.fold_left
                    (fun uu____81206  ->
                       fun elt  ->
                         match uu____81206 with
                         | (g',inversions) ->
                             let uu____81234 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81257  ->
                                       match uu___646_81257 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81259;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81260;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81261;_}
                                           -> false
                                       | uu____81268 -> true))
                                in
                             (match uu____81234 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_81293 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_81293.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_81293.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_81293.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81182 with
                 | (g',inversions) ->
                     let uu____81312 =
                       FStar_List.fold_left
                         (fun uu____81343  ->
                            fun elt  ->
                              match uu____81343 with
                              | (decls,elts,rest) ->
                                  let uu____81384 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81393  ->
                                            match uu___647_81393 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81395 -> true
                                            | uu____81408 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81384
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81431 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81452  ->
                                               match uu___648_81452 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81454 -> true
                                               | uu____81467 -> false))
                                        in
                                     match uu____81431 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_81498 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_81498.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_81498.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_81498.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81312 with
                      | (decls,elts,rest) ->
                          let uu____81524 =
                            let uu____81525 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81532 =
                              let uu____81535 =
                                let uu____81538 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81538  in
                              FStar_List.append elts uu____81535  in
                            FStar_List.append uu____81525 uu____81532  in
                          (uu____81524, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81549,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81562 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81562 with
             | (usubst,uvs) ->
                 let uu____81582 =
                   let uu____81589 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81590 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81591 =
                     let uu____81592 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81592 k  in
                   (uu____81589, uu____81590, uu____81591)  in
                 (match uu____81582 with
                  | (env1,tps1,k1) ->
                      let uu____81605 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81605 with
                       | (tps2,k2) ->
                           let uu____81613 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81613 with
                            | (uu____81629,k3) ->
                                let uu____81651 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81651 with
                                 | (tps3,env_tps,uu____81663,us) ->
                                     let u_k =
                                       let uu____81666 =
                                         let uu____81667 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81668 =
                                           let uu____81673 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81675 =
                                             let uu____81676 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81676
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81673 uu____81675
                                            in
                                         uu____81668
                                           FStar_Pervasives_Native.None
                                           uu____81667
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81666 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81694) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81700,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81703) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81711,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81718) ->
                                           let uu____81719 =
                                             let uu____81721 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81721
                                              in
                                           failwith uu____81719
                                       | (uu____81725,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81726 =
                                             let uu____81728 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81728
                                              in
                                           failwith uu____81726
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81732,uu____81733) ->
                                           let uu____81742 =
                                             let uu____81744 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81744
                                              in
                                           failwith uu____81742
                                       | (uu____81748,FStar_Syntax_Syntax.U_unif
                                          uu____81749) ->
                                           let uu____81758 =
                                             let uu____81760 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81760
                                              in
                                           failwith uu____81758
                                       | uu____81764 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81777 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81777 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81795 = u_leq_u_k u_tp  in
                                       if uu____81795
                                       then true
                                       else
                                         (let uu____81802 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81802 with
                                          | (formals,uu____81819) ->
                                              let uu____81840 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81840 with
                                               | (uu____81850,uu____81851,uu____81852,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81863 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81863
             then
               let uu____81868 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81868
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81888  ->
                       match uu___649_81888 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81892 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81905 = c  in
                 match uu____81905 with
                 | (name,args,uu____81910,uu____81911,uu____81912) ->
                     let uu____81923 =
                       let uu____81924 =
                         let uu____81936 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____81963  ->
                                   match uu____81963 with
                                   | (uu____81972,sort,uu____81974) -> sort))
                            in
                         (name, uu____81936,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81924  in
                     [uu____81923]
               else
                 (let uu____81985 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____81985 c)
                in
             let inversion_axioms tapp vars =
               let uu____82003 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____82011 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____82011 FStar_Option.isNone))
                  in
               if uu____82003
               then []
               else
                 (let uu____82046 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82046 with
                  | (xxsym,xx) ->
                      let uu____82059 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82098  ->
                                fun l  ->
                                  match uu____82098 with
                                  | (out,decls) ->
                                      let uu____82118 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82118 with
                                       | (uu____82129,data_t) ->
                                           let uu____82131 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82131 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82175 =
                                                    let uu____82176 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82176.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82175 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82179,indices)
                                                      -> indices
                                                  | uu____82205 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82235  ->
                                                            match uu____82235
                                                            with
                                                            | (x,uu____82243)
                                                                ->
                                                                let uu____82248
                                                                  =
                                                                  let uu____82249
                                                                    =
                                                                    let uu____82257
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82257,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82249
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82248)
                                                       env)
                                                   in
                                                let uu____82262 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82262 with
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
                                                                  let uu____82297
                                                                    =
                                                                    let uu____82302
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82302,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82297)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82305 =
                                                         let uu____82306 =
                                                           let uu____82311 =
                                                             let uu____82312
                                                               =
                                                               let uu____82317
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82318
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82317,
                                                                 uu____82318)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82312
                                                              in
                                                           (out, uu____82311)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82306
                                                          in
                                                       (uu____82305,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82059 with
                       | (data_ax,decls) ->
                           let uu____82333 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82333 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82350 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82350 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82357 =
                                    let uu____82365 =
                                      let uu____82366 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82367 =
                                        let uu____82378 =
                                          let uu____82379 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82381 =
                                            let uu____82384 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82384 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82379 uu____82381
                                           in
                                        let uu____82386 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82378,
                                          uu____82386)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82366 uu____82367
                                       in
                                    let uu____82395 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82365,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82395)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82357
                                   in
                                let uu____82401 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82401)))
                in
             let uu____82408 =
               let uu____82413 =
                 let uu____82414 = FStar_Syntax_Subst.compress k  in
                 uu____82414.FStar_Syntax_Syntax.n  in
               match uu____82413 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____82449 -> (tps, k)  in
             match uu____82408 with
             | (formals,res) ->
                 let uu____82456 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____82456 with
                  | (formals1,res1) ->
                      let uu____82467 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____82467 with
                       | (vars,guards,env',binder_decls,uu____82492) ->
                           let arity = FStar_List.length vars  in
                           let uu____82506 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____82506 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____82532 =
                                    let uu____82540 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____82540)  in
                                  FStar_SMTEncoding_Util.mkApp uu____82532
                                   in
                                let uu____82546 =
                                  let tname_decl =
                                    let uu____82556 =
                                      let uu____82557 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____82576 =
                                                  let uu____82578 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____82578
                                                   in
                                                let uu____82580 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____82576, uu____82580,
                                                  false)))
                                         in
                                      let uu____82584 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____82557,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____82584, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____82556
                                     in
                                  let uu____82592 =
                                    match vars with
                                    | [] ->
                                        let uu____82605 =
                                          let uu____82606 =
                                            let uu____82609 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _82615  ->
                                                 FStar_Pervasives_Native.Some
                                                   _82615) uu____82609
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____82606
                                           in
                                        ([], uu____82605)
                                    | uu____82618 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____82628 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____82628
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____82644 =
                                            let uu____82652 =
                                              let uu____82653 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____82654 =
                                                let uu____82670 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____82670)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____82653 uu____82654
                                               in
                                            (uu____82652,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____82644
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____82592 with
                                  | (tok_decls,env2) ->
                                      let uu____82697 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____82697
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____82546 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____82725 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____82725 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____82747 =
                                                 let uu____82748 =
                                                   let uu____82756 =
                                                     let uu____82757 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____82757
                                                      in
                                                   (uu____82756,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____82748
                                                  in
                                               [uu____82747]
                                             else []  in
                                           let uu____82765 =
                                             let uu____82768 =
                                               let uu____82771 =
                                                 let uu____82774 =
                                                   let uu____82775 =
                                                     let uu____82783 =
                                                       let uu____82784 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____82785 =
                                                         let uu____82796 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____82796)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____82784
                                                         uu____82785
                                                        in
                                                     (uu____82783,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____82775
                                                    in
                                                 [uu____82774]  in
                                               FStar_List.append karr
                                                 uu____82771
                                                in
                                             FStar_All.pipe_right uu____82768
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____82765
                                        in
                                     let aux =
                                       let uu____82815 =
                                         let uu____82818 =
                                           inversion_axioms tapp vars  in
                                         let uu____82821 =
                                           let uu____82824 =
                                             let uu____82827 =
                                               let uu____82828 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____82828 env2
                                                 tapp vars
                                                in
                                             [uu____82827]  in
                                           FStar_All.pipe_right uu____82824
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____82818
                                           uu____82821
                                          in
                                       FStar_List.append kindingAx
                                         uu____82815
                                        in
                                     let g =
                                       let uu____82836 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____82836
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82844,uu____82845,uu____82846,uu____82847,uu____82848)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82856,t,uu____82858,n_tps,uu____82860) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____82870 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____82870 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82918 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82918 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____82942 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____82942 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____82962 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____82962 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83041 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83041,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83048 =
                                   let uu____83049 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83049, true)
                                    in
                                 let uu____83057 =
                                   let uu____83064 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83064
                                    in
                                 FStar_All.pipe_right uu____83048 uu____83057
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
                               let uu____83076 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____83076 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83088::uu____83089 ->
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
                                            let uu____83138 =
                                              let uu____83139 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83139]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83138
                                             in
                                          let uu____83165 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83166 =
                                            let uu____83177 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83177)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83165 uu____83166
                                      | uu____83204 -> tok_typing  in
                                    let uu____83215 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83215 with
                                     | (vars',guards',env'',decls_formals,uu____83240)
                                         ->
                                         let uu____83253 =
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
                                         (match uu____83253 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83283 ->
                                                    let uu____83292 =
                                                      let uu____83293 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83293
                                                       in
                                                    [uu____83292]
                                                 in
                                              let encode_elim uu____83309 =
                                                let uu____83310 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83310 with
                                                | (head1,args) ->
                                                    let uu____83361 =
                                                      let uu____83362 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83362.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83361 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83374;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83375;_},uu____83376)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83382 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83382
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
                                                                  | uu____83445
                                                                    ->
                                                                    let uu____83446
                                                                    =
                                                                    let uu____83452
                                                                    =
                                                                    let uu____83454
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83454
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83452)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83446
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83477
                                                                    =
                                                                    let uu____83479
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83479
                                                                     in
                                                                    if
                                                                    uu____83477
                                                                    then
                                                                    let uu____83501
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83501]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83504
                                                                =
                                                                let uu____83518
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83575
                                                                     ->
                                                                    fun
                                                                    uu____83576
                                                                     ->
                                                                    match 
                                                                    (uu____83575,
                                                                    uu____83576)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83687
                                                                    =
                                                                    let uu____83695
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83695
                                                                     in
                                                                    (match uu____83687
                                                                    with
                                                                    | 
                                                                    (uu____83709,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83720
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83720
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83725
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83725
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
                                                                  uu____83518
                                                                 in
                                                              (match uu____83504
                                                               with
                                                               | (uu____83746,arg_vars,elim_eqns_or_guards,uu____83749)
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
                                                                    let uu____83776
                                                                    =
                                                                    let uu____83784
                                                                    =
                                                                    let uu____83785
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83786
                                                                    =
                                                                    let uu____83797
                                                                    =
                                                                    let uu____83798
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83798
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83800
                                                                    =
                                                                    let uu____83801
                                                                    =
                                                                    let uu____83806
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83806)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83801
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83797,
                                                                    uu____83800)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83785
                                                                    uu____83786
                                                                     in
                                                                    (uu____83784,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83776
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83821
                                                                    =
                                                                    let uu____83822
                                                                    =
                                                                    let uu____83828
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83828,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83822
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83821
                                                                     in
                                                                    let uu____83831
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83831
                                                                    then
                                                                    let x =
                                                                    let uu____83835
                                                                    =
                                                                    let uu____83841
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83841,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83835
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83846
                                                                    =
                                                                    let uu____83854
                                                                    =
                                                                    let uu____83855
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83856
                                                                    =
                                                                    let uu____83867
                                                                    =
                                                                    let uu____83872
                                                                    =
                                                                    let uu____83875
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83875]
                                                                     in
                                                                    [uu____83872]
                                                                     in
                                                                    let uu____83880
                                                                    =
                                                                    let uu____83881
                                                                    =
                                                                    let uu____83886
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83888
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83886,
                                                                    uu____83888)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83881
                                                                     in
                                                                    (uu____83867,
                                                                    [x],
                                                                    uu____83880)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83855
                                                                    uu____83856
                                                                     in
                                                                    let uu____83909
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83854,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83909)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83846
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83920
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
                                                                    (let uu____83943
                                                                    =
                                                                    let uu____83944
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____83944
                                                                    dapp1  in
                                                                    [uu____83943])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83920
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____83951
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    let uu____83960
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83961
                                                                    =
                                                                    let uu____83972
                                                                    =
                                                                    let uu____83973
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83973
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83975
                                                                    =
                                                                    let uu____83976
                                                                    =
                                                                    let uu____83981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____83981)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83976
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83972,
                                                                    uu____83975)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83960
                                                                    uu____83961
                                                                     in
                                                                    (uu____83959,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83951)
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
                                                         let uu____84000 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84000
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
                                                                  | uu____84063
                                                                    ->
                                                                    let uu____84064
                                                                    =
                                                                    let uu____84070
                                                                    =
                                                                    let uu____84072
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84072
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84070)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84064
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84095
                                                                    =
                                                                    let uu____84097
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84097
                                                                     in
                                                                    if
                                                                    uu____84095
                                                                    then
                                                                    let uu____84119
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84119]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84122
                                                                =
                                                                let uu____84136
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84193
                                                                     ->
                                                                    fun
                                                                    uu____84194
                                                                     ->
                                                                    match 
                                                                    (uu____84193,
                                                                    uu____84194)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84305
                                                                    =
                                                                    let uu____84313
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84313
                                                                     in
                                                                    (match uu____84305
                                                                    with
                                                                    | 
                                                                    (uu____84327,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84338
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84338
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84343
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84343
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
                                                                  uu____84136
                                                                 in
                                                              (match uu____84122
                                                               with
                                                               | (uu____84364,arg_vars,elim_eqns_or_guards,uu____84367)
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
                                                                    let uu____84394
                                                                    =
                                                                    let uu____84402
                                                                    =
                                                                    let uu____84403
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84404
                                                                    =
                                                                    let uu____84415
                                                                    =
                                                                    let uu____84416
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84416
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84418
                                                                    =
                                                                    let uu____84419
                                                                    =
                                                                    let uu____84424
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84424)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84419
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84415,
                                                                    uu____84418)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84403
                                                                    uu____84404
                                                                     in
                                                                    (uu____84402,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84394
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84439
                                                                    =
                                                                    let uu____84440
                                                                    =
                                                                    let uu____84446
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84446,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84440
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84439
                                                                     in
                                                                    let uu____84449
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84449
                                                                    then
                                                                    let x =
                                                                    let uu____84453
                                                                    =
                                                                    let uu____84459
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84459,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84453
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84464
                                                                    =
                                                                    let uu____84472
                                                                    =
                                                                    let uu____84473
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84474
                                                                    =
                                                                    let uu____84485
                                                                    =
                                                                    let uu____84490
                                                                    =
                                                                    let uu____84493
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84493]
                                                                     in
                                                                    [uu____84490]
                                                                     in
                                                                    let uu____84498
                                                                    =
                                                                    let uu____84499
                                                                    =
                                                                    let uu____84504
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84506
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84504,
                                                                    uu____84506)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84499
                                                                     in
                                                                    (uu____84485,
                                                                    [x],
                                                                    uu____84498)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84473
                                                                    uu____84474
                                                                     in
                                                                    let uu____84527
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84472,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84527)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84464
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84538
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
                                                                    (let uu____84561
                                                                    =
                                                                    let uu____84562
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84562
                                                                    dapp1  in
                                                                    [uu____84561])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84538
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84569
                                                                    =
                                                                    let uu____84577
                                                                    =
                                                                    let uu____84578
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84579
                                                                    =
                                                                    let uu____84590
                                                                    =
                                                                    let uu____84591
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84591
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84593
                                                                    =
                                                                    let uu____84594
                                                                    =
                                                                    let uu____84599
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84599)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84594
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84590,
                                                                    uu____84593)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84578
                                                                    uu____84579
                                                                     in
                                                                    (uu____84577,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84569)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84616 ->
                                                         ((let uu____84618 =
                                                             let uu____84624
                                                               =
                                                               let uu____84626
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84628
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84626
                                                                 uu____84628
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84624)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84618);
                                                          ([], [])))
                                                 in
                                              let uu____84636 =
                                                encode_elim ()  in
                                              (match uu____84636 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84662 =
                                                       let uu____84665 =
                                                         let uu____84668 =
                                                           let uu____84671 =
                                                             let uu____84674
                                                               =
                                                               let uu____84677
                                                                 =
                                                                 let uu____84680
                                                                   =
                                                                   let uu____84681
                                                                    =
                                                                    let uu____84693
                                                                    =
                                                                    let uu____84694
                                                                    =
                                                                    let uu____84696
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84696
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84694
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84693)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84681
                                                                    in
                                                                 [uu____84680]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84677
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84674
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84707 =
                                                             let uu____84710
                                                               =
                                                               let uu____84713
                                                                 =
                                                                 let uu____84716
                                                                   =
                                                                   let uu____84719
                                                                    =
                                                                    let uu____84722
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84727
                                                                    =
                                                                    let uu____84730
                                                                    =
                                                                    let uu____84731
                                                                    =
                                                                    let uu____84739
                                                                    =
                                                                    let uu____84740
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84741
                                                                    =
                                                                    let uu____84752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84752)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84740
                                                                    uu____84741
                                                                     in
                                                                    (uu____84739,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84731
                                                                     in
                                                                    let uu____84765
                                                                    =
                                                                    let uu____84768
                                                                    =
                                                                    let uu____84769
                                                                    =
                                                                    let uu____84777
                                                                    =
                                                                    let uu____84778
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84779
                                                                    =
                                                                    let uu____84790
                                                                    =
                                                                    let uu____84791
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84791
                                                                    vars'  in
                                                                    let uu____84793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84790,
                                                                    uu____84793)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84778
                                                                    uu____84779
                                                                     in
                                                                    (uu____84777,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84769
                                                                     in
                                                                    [uu____84768]
                                                                     in
                                                                    uu____84730
                                                                    ::
                                                                    uu____84765
                                                                     in
                                                                    uu____84722
                                                                    ::
                                                                    uu____84727
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84719
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84716
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84713
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84710
                                                              in
                                                           FStar_List.append
                                                             uu____84671
                                                             uu____84707
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84668
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84665
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84662
                                                      in
                                                   let uu____84810 =
                                                     let uu____84811 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84811 g
                                                      in
                                                   (uu____84810, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84845  ->
              fun se  ->
                match uu____84845 with
                | (g,env1) ->
                    let uu____84865 = encode_sigelt env1 se  in
                    (match uu____84865 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____84933 =
        match uu____84933 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____84970 ->
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
                 ((let uu____84978 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____84978
                   then
                     let uu____84983 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____84985 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____84987 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____84983 uu____84985 uu____84987
                   else ());
                  (let uu____84992 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____84992 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____85010 =
                         let uu____85018 =
                           let uu____85020 =
                             let uu____85022 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85022
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85020  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85018
                          in
                       (match uu____85010 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85042 = FStar_Options.log_queries ()
                                 in
                              if uu____85042
                              then
                                let uu____85045 =
                                  let uu____85047 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85049 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85051 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85047 uu____85049 uu____85051
                                   in
                                FStar_Pervasives_Native.Some uu____85045
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85067 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85077 =
                                let uu____85080 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85080  in
                              FStar_List.append uu____85067 uu____85077  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85092,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85112 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85112 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85133 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85133 with | (uu____85160,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85213  ->
              match uu____85213 with
              | (l,uu____85222,uu____85223) ->
                  let uu____85226 =
                    let uu____85238 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85238, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85226))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85271  ->
              match uu____85271 with
              | (l,uu____85282,uu____85283) ->
                  let uu____85286 =
                    let uu____85287 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85290  -> FStar_SMTEncoding_Term.Echo _85290)
                      uu____85287
                     in
                  let uu____85291 =
                    let uu____85294 =
                      let uu____85295 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85295  in
                    [uu____85294]  in
                  uu____85286 :: uu____85291))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85313 =
      let uu____85316 =
        let uu____85317 = FStar_Util.psmap_empty ()  in
        let uu____85332 =
          let uu____85341 = FStar_Util.psmap_empty ()  in (uu____85341, [])
           in
        let uu____85348 =
          let uu____85350 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85350 FStar_Ident.string_of_lid  in
        let uu____85352 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85317;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85332;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85348;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85352
        }  in
      [uu____85316]  in
    FStar_ST.op_Colon_Equals last_env uu____85313
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85396 = FStar_ST.op_Bang last_env  in
      match uu____85396 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85424 ->
          let uu___2175_85427 = e  in
          let uu____85428 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_85427.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_85427.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_85427.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_85427.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_85427.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_85427.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_85427.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85428;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_85427.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_85427.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85436 = FStar_ST.op_Bang last_env  in
    match uu____85436 with
    | [] -> failwith "Empty env stack"
    | uu____85463::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85495  ->
    let uu____85496 = FStar_ST.op_Bang last_env  in
    match uu____85496 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85556  ->
    let uu____85557 = FStar_ST.op_Bang last_env  in
    match uu____85557 with
    | [] -> failwith "Popping an empty stack"
    | uu____85584::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85621  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85674  ->
         let uu____85675 = snapshot_env ()  in
         match uu____85675 with
         | (env_depth,()) ->
             let uu____85697 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85697 with
              | (varops_depth,()) ->
                  let uu____85719 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85719 with
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
        (fun uu____85777  ->
           let uu____85778 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85778 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85873 = snapshot msg  in () 
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
        | (uu____85919::uu____85920,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_85928 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_85928.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_85928.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_85928.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____85929 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_85956 = elt  in
        let uu____85957 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_85956.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_85956.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____85957;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_85956.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____85977 =
        let uu____85980 =
          let uu____85981 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____85981  in
        let uu____85982 = open_fact_db_tags env  in uu____85980 ::
          uu____85982
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____85977
  
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
      let uu____86009 = encode_sigelt env se  in
      match uu____86009 with
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
                (let uu____86055 =
                   let uu____86058 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86058
                    in
                 match uu____86055 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86073 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86073
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86103 = FStar_Options.log_queries ()  in
        if uu____86103
        then
          let uu____86108 =
            let uu____86109 =
              let uu____86111 =
                let uu____86113 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86113 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86111  in
            FStar_SMTEncoding_Term.Caption uu____86109  in
          uu____86108 :: decls
        else decls  in
      (let uu____86132 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86132
       then
         let uu____86135 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86135
       else ());
      (let env =
         let uu____86141 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86141 tcenv  in
       let uu____86142 = encode_top_level_facts env se  in
       match uu____86142 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86156 =
               let uu____86159 =
                 let uu____86162 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86162
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86159  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86156)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86195 = FStar_Options.log_queries ()  in
          if uu____86195
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_86215 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_86215.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_86215.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_86215.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_86215.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_86215.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_86215.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_86215.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_86215.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_86215.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_86215.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86220 =
             let uu____86223 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86223
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86220  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86243 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86243
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
          (let uu____86267 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86267
           then
             let uu____86270 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86270
           else ());
          (let env =
             let uu____86278 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86278
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86317  ->
                     fun se  ->
                       match uu____86317 with
                       | (g,env2) ->
                           let uu____86337 = encode_top_level_facts env2 se
                              in
                           (match uu____86337 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86360 =
             encode_signature
               (let uu___2303_86369 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_86369.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_86369.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_86369.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_86369.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_86369.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_86369.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_86369.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_86369.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_86369.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_86369.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86360 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86385 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86385
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86391 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86391))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86419  ->
        match uu____86419 with
        | (decls,fvbs) ->
            ((let uu____86433 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86433
              then ()
              else
                (let uu____86438 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86438
                 then
                   let uu____86441 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86441
                 else ()));
             (let env =
                let uu____86449 = get_env name tcenv  in
                FStar_All.pipe_right uu____86449
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86451 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86451
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86465 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86465
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
        (let uu____86527 =
           let uu____86529 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86529.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86527);
        (let env =
           let uu____86531 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86531 tcenv  in
         let uu____86532 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86571 = aux rest  in
                 (match uu____86571 with
                  | (out,rest1) ->
                      let t =
                        let uu____86599 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86599 with
                        | FStar_Pervasives_Native.Some uu____86602 ->
                            let uu____86603 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86603
                              x.FStar_Syntax_Syntax.sort
                        | uu____86604 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86608 =
                        let uu____86611 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_86614 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_86614.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_86614.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86611 :: out  in
                      (uu____86608, rest1))
             | uu____86619 -> ([], bindings)  in
           let uu____86626 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86626 with
           | (closing,bindings) ->
               let uu____86653 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86653, bindings)
            in
         match uu____86532 with
         | (q1,bindings) ->
             let uu____86684 = encode_env_bindings env bindings  in
             (match uu____86684 with
              | (env_decls,env1) ->
                  ((let uu____86706 =
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
                    if uu____86706
                    then
                      let uu____86713 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86713
                    else ());
                   (let uu____86718 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86718 with
                    | (phi,qdecls) ->
                        let uu____86739 =
                          let uu____86744 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86744 phi
                           in
                        (match uu____86739 with
                         | (labels,phi1) ->
                             let uu____86761 = encode_labels labels  in
                             (match uu____86761 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86797 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86797
                                    then
                                      let uu____86802 =
                                        let uu____86803 =
                                          let uu____86805 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86805
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86803
                                         in
                                      [uu____86802]
                                    else []  in
                                  let query_prelude =
                                    let uu____86813 =
                                      let uu____86814 =
                                        let uu____86815 =
                                          let uu____86818 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86825 =
                                            let uu____86828 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86828
                                             in
                                          FStar_List.append uu____86818
                                            uu____86825
                                           in
                                        FStar_List.append env_decls
                                          uu____86815
                                         in
                                      FStar_All.pipe_right uu____86814
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86813
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86838 =
                                      let uu____86846 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86847 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86846,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86847)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86838
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
  