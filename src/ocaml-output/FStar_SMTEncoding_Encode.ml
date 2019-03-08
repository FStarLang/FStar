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
  let uu____67880 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67880 with
  | (asym,a) ->
      let uu____67891 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67891 with
       | (xsym,x) ->
           let uu____67902 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67902 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____67980 =
                      let uu____67992 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____67992, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____67980  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68012 =
                      let uu____68020 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68020)  in
                    FStar_SMTEncoding_Util.mkApp uu____68012  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68039 =
                    let uu____68042 =
                      let uu____68045 =
                        let uu____68048 =
                          let uu____68049 =
                            let uu____68057 =
                              let uu____68058 =
                                let uu____68069 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68069)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68058
                               in
                            (uu____68057, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68049  in
                        let uu____68081 =
                          let uu____68084 =
                            let uu____68085 =
                              let uu____68093 =
                                let uu____68094 =
                                  let uu____68105 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68105)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68094
                                 in
                              (uu____68093,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68085  in
                          [uu____68084]  in
                        uu____68048 :: uu____68081  in
                      xtok_decl :: uu____68045  in
                    xname_decl :: uu____68042  in
                  (xtok1, (FStar_List.length vars), uu____68039)  in
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
                  let uu____68275 =
                    let uu____68296 =
                      let uu____68315 =
                        let uu____68316 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68316
                         in
                      quant axy uu____68315  in
                    (FStar_Parser_Const.op_Eq, uu____68296)  in
                  let uu____68333 =
                    let uu____68356 =
                      let uu____68377 =
                        let uu____68396 =
                          let uu____68397 =
                            let uu____68398 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68398  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68397
                           in
                        quant axy uu____68396  in
                      (FStar_Parser_Const.op_notEq, uu____68377)  in
                    let uu____68415 =
                      let uu____68438 =
                        let uu____68459 =
                          let uu____68478 =
                            let uu____68479 =
                              let uu____68480 =
                                let uu____68485 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68486 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68485, uu____68486)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68480  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68479
                             in
                          quant xy uu____68478  in
                        (FStar_Parser_Const.op_And, uu____68459)  in
                      let uu____68503 =
                        let uu____68526 =
                          let uu____68547 =
                            let uu____68566 =
                              let uu____68567 =
                                let uu____68568 =
                                  let uu____68573 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68574 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68573, uu____68574)  in
                                FStar_SMTEncoding_Util.mkOr uu____68568  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68567
                               in
                            quant xy uu____68566  in
                          (FStar_Parser_Const.op_Or, uu____68547)  in
                        let uu____68591 =
                          let uu____68614 =
                            let uu____68635 =
                              let uu____68654 =
                                let uu____68655 =
                                  let uu____68656 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68656
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68655
                                 in
                              quant qx uu____68654  in
                            (FStar_Parser_Const.op_Negation, uu____68635)  in
                          let uu____68673 =
                            let uu____68696 =
                              let uu____68717 =
                                let uu____68736 =
                                  let uu____68737 =
                                    let uu____68738 =
                                      let uu____68743 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68744 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68743, uu____68744)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68738
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68737
                                   in
                                quant xy uu____68736  in
                              (FStar_Parser_Const.op_LT, uu____68717)  in
                            let uu____68761 =
                              let uu____68784 =
                                let uu____68805 =
                                  let uu____68824 =
                                    let uu____68825 =
                                      let uu____68826 =
                                        let uu____68831 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68832 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68831, uu____68832)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68826
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68825
                                     in
                                  quant xy uu____68824  in
                                (FStar_Parser_Const.op_LTE, uu____68805)  in
                              let uu____68849 =
                                let uu____68872 =
                                  let uu____68893 =
                                    let uu____68912 =
                                      let uu____68913 =
                                        let uu____68914 =
                                          let uu____68919 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68920 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68919, uu____68920)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68914
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68913
                                       in
                                    quant xy uu____68912  in
                                  (FStar_Parser_Const.op_GT, uu____68893)  in
                                let uu____68937 =
                                  let uu____68960 =
                                    let uu____68981 =
                                      let uu____69000 =
                                        let uu____69001 =
                                          let uu____69002 =
                                            let uu____69007 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69008 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69007, uu____69008)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69002
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69001
                                         in
                                      quant xy uu____69000  in
                                    (FStar_Parser_Const.op_GTE, uu____68981)
                                     in
                                  let uu____69025 =
                                    let uu____69048 =
                                      let uu____69069 =
                                        let uu____69088 =
                                          let uu____69089 =
                                            let uu____69090 =
                                              let uu____69095 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69096 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69095, uu____69096)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69090
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69089
                                           in
                                        quant xy uu____69088  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69069)
                                       in
                                    let uu____69113 =
                                      let uu____69136 =
                                        let uu____69157 =
                                          let uu____69176 =
                                            let uu____69177 =
                                              let uu____69178 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69178
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69177
                                             in
                                          quant qx uu____69176  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69157)
                                         in
                                      let uu____69195 =
                                        let uu____69218 =
                                          let uu____69239 =
                                            let uu____69258 =
                                              let uu____69259 =
                                                let uu____69260 =
                                                  let uu____69265 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69266 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69265, uu____69266)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69260
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69259
                                               in
                                            quant xy uu____69258  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69239)
                                           in
                                        let uu____69283 =
                                          let uu____69306 =
                                            let uu____69327 =
                                              let uu____69346 =
                                                let uu____69347 =
                                                  let uu____69348 =
                                                    let uu____69353 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69354 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69353,
                                                      uu____69354)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69348
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69347
                                                 in
                                              quant xy uu____69346  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69327)
                                             in
                                          let uu____69371 =
                                            let uu____69394 =
                                              let uu____69415 =
                                                let uu____69434 =
                                                  let uu____69435 =
                                                    let uu____69436 =
                                                      let uu____69441 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69442 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69441,
                                                        uu____69442)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69436
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69435
                                                   in
                                                quant xy uu____69434  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69415)
                                               in
                                            let uu____69459 =
                                              let uu____69482 =
                                                let uu____69503 =
                                                  let uu____69522 =
                                                    let uu____69523 =
                                                      let uu____69524 =
                                                        let uu____69529 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69530 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69529,
                                                          uu____69530)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69524
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69523
                                                     in
                                                  quant xy uu____69522  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69503)
                                                 in
                                              let uu____69547 =
                                                let uu____69570 =
                                                  let uu____69591 =
                                                    let uu____69610 =
                                                      let uu____69611 =
                                                        let uu____69612 =
                                                          let uu____69617 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69618 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69617,
                                                            uu____69618)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69612
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69611
                                                       in
                                                    quant xy uu____69610  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69591)
                                                   in
                                                let uu____69635 =
                                                  let uu____69658 =
                                                    let uu____69679 =
                                                      let uu____69698 =
                                                        let uu____69699 =
                                                          let uu____69700 =
                                                            let uu____69705 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69706 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69705,
                                                              uu____69706)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69700
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69699
                                                         in
                                                      quant xy uu____69698
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69679)
                                                     in
                                                  let uu____69723 =
                                                    let uu____69746 =
                                                      let uu____69767 =
                                                        let uu____69786 =
                                                          let uu____69787 =
                                                            let uu____69788 =
                                                              let uu____69793
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69794
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69793,
                                                                uu____69794)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69788
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69787
                                                           in
                                                        quant xy uu____69786
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69767)
                                                       in
                                                    let uu____69811 =
                                                      let uu____69834 =
                                                        let uu____69855 =
                                                          let uu____69874 =
                                                            let uu____69875 =
                                                              let uu____69876
                                                                =
                                                                let uu____69881
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69882
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69881,
                                                                  uu____69882)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69876
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69875
                                                             in
                                                          quant xy
                                                            uu____69874
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69855)
                                                         in
                                                      let uu____69899 =
                                                        let uu____69922 =
                                                          let uu____69943 =
                                                            let uu____69962 =
                                                              let uu____69963
                                                                =
                                                                let uu____69964
                                                                  =
                                                                  let uu____69969
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____69970
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____69969,
                                                                    uu____69970)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____69964
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____69963
                                                               in
                                                            quant xy
                                                              uu____69962
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69943)
                                                           in
                                                        let uu____69987 =
                                                          let uu____70010 =
                                                            let uu____70031 =
                                                              let uu____70050
                                                                =
                                                                let uu____70051
                                                                  =
                                                                  let uu____70052
                                                                    =
                                                                    let uu____70057
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70058
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70057,
                                                                    uu____70058)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70052
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70051
                                                                 in
                                                              quant xy
                                                                uu____70050
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70031)
                                                             in
                                                          let uu____70075 =
                                                            let uu____70098 =
                                                              let uu____70119
                                                                =
                                                                let uu____70138
                                                                  =
                                                                  let uu____70139
                                                                    =
                                                                    let uu____70140
                                                                    =
                                                                    let uu____70145
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70146
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70145,
                                                                    uu____70146)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70140
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70139
                                                                   in
                                                                quant xy
                                                                  uu____70138
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70119)
                                                               in
                                                            let uu____70163 =
                                                              let uu____70186
                                                                =
                                                                let uu____70207
                                                                  =
                                                                  let uu____70226
                                                                    =
                                                                    let uu____70227
                                                                    =
                                                                    let uu____70228
                                                                    =
                                                                    let uu____70233
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70234
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70233,
                                                                    uu____70234)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70228
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70227
                                                                     in
                                                                  quant xy
                                                                    uu____70226
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70207)
                                                                 in
                                                              let uu____70251
                                                                =
                                                                let uu____70274
                                                                  =
                                                                  let uu____70295
                                                                    =
                                                                    let uu____70314
                                                                    =
                                                                    let uu____70315
                                                                    =
                                                                    let uu____70316
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70316
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70315
                                                                     in
                                                                    quant qx
                                                                    uu____70314
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70295)
                                                                   in
                                                                [uu____70274]
                                                                 in
                                                              uu____70186 ::
                                                                uu____70251
                                                               in
                                                            uu____70098 ::
                                                              uu____70163
                                                             in
                                                          uu____70010 ::
                                                            uu____70075
                                                           in
                                                        uu____69922 ::
                                                          uu____69987
                                                         in
                                                      uu____69834 ::
                                                        uu____69899
                                                       in
                                                    uu____69746 ::
                                                      uu____69811
                                                     in
                                                  uu____69658 :: uu____69723
                                                   in
                                                uu____69570 :: uu____69635
                                                 in
                                              uu____69482 :: uu____69547  in
                                            uu____69394 :: uu____69459  in
                                          uu____69306 :: uu____69371  in
                                        uu____69218 :: uu____69283  in
                                      uu____69136 :: uu____69195  in
                                    uu____69048 :: uu____69113  in
                                  uu____68960 :: uu____69025  in
                                uu____68872 :: uu____68937  in
                              uu____68784 :: uu____68849  in
                            uu____68696 :: uu____68761  in
                          uu____68614 :: uu____68673  in
                        uu____68526 :: uu____68591  in
                      uu____68438 :: uu____68503  in
                    uu____68356 :: uu____68415  in
                  uu____68275 :: uu____68333  in
                let mk1 l v1 =
                  let uu____70855 =
                    let uu____70867 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____70957  ->
                              match uu____70957 with
                              | (l',uu____70978) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70867
                      (FStar_Option.map
                         (fun uu____71077  ->
                            match uu____71077 with
                            | (uu____71105,b) ->
                                let uu____71139 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71139 v1))
                     in
                  FStar_All.pipe_right uu____70855 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71222  ->
                          match uu____71222 with
                          | (l',uu____71243) -> FStar_Ident.lid_equals l l'))
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
          let uu____71317 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71317 with
          | (xxsym,xx) ->
              let uu____71328 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71328 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71344 =
                     let uu____71352 =
                       let uu____71353 =
                         let uu____71364 =
                           let uu____71365 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71375 =
                             let uu____71386 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71386 :: vars  in
                           uu____71365 :: uu____71375  in
                         let uu____71412 =
                           let uu____71413 =
                             let uu____71418 =
                               let uu____71419 =
                                 let uu____71424 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71424)  in
                               FStar_SMTEncoding_Util.mkEq uu____71419  in
                             (xx_has_type, uu____71418)  in
                           FStar_SMTEncoding_Util.mkImp uu____71413  in
                         ([[xx_has_type]], uu____71364, uu____71412)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71353  in
                     let uu____71437 =
                       let uu____71439 =
                         let uu____71441 =
                           let uu____71443 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71443  in
                         Prims.op_Hat module_name uu____71441  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71439
                        in
                     (uu____71352,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71437)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71344)
  
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
    let uu____71499 =
      let uu____71501 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71501  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71499  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71523 =
      let uu____71524 =
        let uu____71532 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71532, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71524  in
    let uu____71537 =
      let uu____71540 =
        let uu____71541 =
          let uu____71549 =
            let uu____71550 =
              let uu____71561 =
                let uu____71562 =
                  let uu____71567 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71567)  in
                FStar_SMTEncoding_Util.mkImp uu____71562  in
              ([[typing_pred]], [xx], uu____71561)  in
            let uu____71592 =
              let uu____71607 = FStar_TypeChecker_Env.get_range env  in
              let uu____71608 = mkForall_fuel1 env  in
              uu____71608 uu____71607  in
            uu____71592 uu____71550  in
          (uu____71549, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71541  in
      [uu____71540]  in
    uu____71523 :: uu____71537  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71655 =
      let uu____71656 =
        let uu____71664 =
          let uu____71665 = FStar_TypeChecker_Env.get_range env  in
          let uu____71666 =
            let uu____71677 =
              let uu____71682 =
                let uu____71685 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71685]  in
              [uu____71682]  in
            let uu____71690 =
              let uu____71691 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71691 tt  in
            (uu____71677, [bb], uu____71690)  in
          FStar_SMTEncoding_Term.mkForall uu____71665 uu____71666  in
        (uu____71664, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71656  in
    let uu____71716 =
      let uu____71719 =
        let uu____71720 =
          let uu____71728 =
            let uu____71729 =
              let uu____71740 =
                let uu____71741 =
                  let uu____71746 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71746)  in
                FStar_SMTEncoding_Util.mkImp uu____71741  in
              ([[typing_pred]], [xx], uu____71740)  in
            let uu____71773 =
              let uu____71788 = FStar_TypeChecker_Env.get_range env  in
              let uu____71789 = mkForall_fuel1 env  in
              uu____71789 uu____71788  in
            uu____71773 uu____71729  in
          (uu____71728, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71720  in
      [uu____71719]  in
    uu____71655 :: uu____71716  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71832 =
        let uu____71833 =
          let uu____71839 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71839, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71833  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71832  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71853 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71853  in
    let uu____71858 =
      let uu____71859 =
        let uu____71867 =
          let uu____71868 = FStar_TypeChecker_Env.get_range env  in
          let uu____71869 =
            let uu____71880 =
              let uu____71885 =
                let uu____71888 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71888]  in
              [uu____71885]  in
            let uu____71893 =
              let uu____71894 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71894 tt  in
            (uu____71880, [bb], uu____71893)  in
          FStar_SMTEncoding_Term.mkForall uu____71868 uu____71869  in
        (uu____71867, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71859  in
    let uu____71919 =
      let uu____71922 =
        let uu____71923 =
          let uu____71931 =
            let uu____71932 =
              let uu____71943 =
                let uu____71944 =
                  let uu____71949 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71949)  in
                FStar_SMTEncoding_Util.mkImp uu____71944  in
              ([[typing_pred]], [xx], uu____71943)  in
            let uu____71976 =
              let uu____71991 = FStar_TypeChecker_Env.get_range env  in
              let uu____71992 = mkForall_fuel1 env  in
              uu____71992 uu____71991  in
            uu____71976 uu____71932  in
          (uu____71931, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71923  in
      let uu____72014 =
        let uu____72017 =
          let uu____72018 =
            let uu____72026 =
              let uu____72027 =
                let uu____72038 =
                  let uu____72039 =
                    let uu____72044 =
                      let uu____72045 =
                        let uu____72048 =
                          let uu____72051 =
                            let uu____72054 =
                              let uu____72055 =
                                let uu____72060 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72061 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72060, uu____72061)  in
                              FStar_SMTEncoding_Util.mkGT uu____72055  in
                            let uu____72063 =
                              let uu____72066 =
                                let uu____72067 =
                                  let uu____72072 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72073 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72072, uu____72073)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72067  in
                              let uu____72075 =
                                let uu____72078 =
                                  let uu____72079 =
                                    let uu____72084 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72085 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72084, uu____72085)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72079  in
                                [uu____72078]  in
                              uu____72066 :: uu____72075  in
                            uu____72054 :: uu____72063  in
                          typing_pred_y :: uu____72051  in
                        typing_pred :: uu____72048  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72045  in
                    (uu____72044, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72039  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72038)
                 in
              let uu____72118 =
                let uu____72133 = FStar_TypeChecker_Env.get_range env  in
                let uu____72134 = mkForall_fuel1 env  in
                uu____72134 uu____72133  in
              uu____72118 uu____72027  in
            (uu____72026,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72018  in
        [uu____72017]  in
      uu____71922 :: uu____72014  in
    uu____71858 :: uu____71919  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72177 =
        let uu____72178 =
          let uu____72184 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72184, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72178  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72177  in
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
      let uu____72200 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72200  in
    let uu____72205 =
      let uu____72206 =
        let uu____72214 =
          let uu____72215 = FStar_TypeChecker_Env.get_range env  in
          let uu____72216 =
            let uu____72227 =
              let uu____72232 =
                let uu____72235 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72235]  in
              [uu____72232]  in
            let uu____72240 =
              let uu____72241 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72241 tt  in
            (uu____72227, [bb], uu____72240)  in
          FStar_SMTEncoding_Term.mkForall uu____72215 uu____72216  in
        (uu____72214, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72206  in
    let uu____72266 =
      let uu____72269 =
        let uu____72270 =
          let uu____72278 =
            let uu____72279 =
              let uu____72290 =
                let uu____72291 =
                  let uu____72296 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72296)  in
                FStar_SMTEncoding_Util.mkImp uu____72291  in
              ([[typing_pred]], [xx], uu____72290)  in
            let uu____72323 =
              let uu____72338 = FStar_TypeChecker_Env.get_range env  in
              let uu____72339 = mkForall_fuel1 env  in
              uu____72339 uu____72338  in
            uu____72323 uu____72279  in
          (uu____72278, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72270  in
      let uu____72361 =
        let uu____72364 =
          let uu____72365 =
            let uu____72373 =
              let uu____72374 =
                let uu____72385 =
                  let uu____72386 =
                    let uu____72391 =
                      let uu____72392 =
                        let uu____72395 =
                          let uu____72398 =
                            let uu____72401 =
                              let uu____72402 =
                                let uu____72407 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72408 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72407, uu____72408)  in
                              FStar_SMTEncoding_Util.mkGT uu____72402  in
                            let uu____72410 =
                              let uu____72413 =
                                let uu____72414 =
                                  let uu____72419 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72420 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72419, uu____72420)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72414  in
                              let uu____72422 =
                                let uu____72425 =
                                  let uu____72426 =
                                    let uu____72431 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72432 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72431, uu____72432)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72426  in
                                [uu____72425]  in
                              uu____72413 :: uu____72422  in
                            uu____72401 :: uu____72410  in
                          typing_pred_y :: uu____72398  in
                        typing_pred :: uu____72395  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72392  in
                    (uu____72391, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72386  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72385)
                 in
              let uu____72465 =
                let uu____72480 = FStar_TypeChecker_Env.get_range env  in
                let uu____72481 = mkForall_fuel1 env  in
                uu____72481 uu____72480  in
              uu____72465 uu____72374  in
            (uu____72373,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72365  in
        [uu____72364]  in
      uu____72269 :: uu____72361  in
    uu____72205 :: uu____72266  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72528 =
      let uu____72529 =
        let uu____72537 =
          let uu____72538 = FStar_TypeChecker_Env.get_range env  in
          let uu____72539 =
            let uu____72550 =
              let uu____72555 =
                let uu____72558 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72558]  in
              [uu____72555]  in
            let uu____72563 =
              let uu____72564 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72564 tt  in
            (uu____72550, [bb], uu____72563)  in
          FStar_SMTEncoding_Term.mkForall uu____72538 uu____72539  in
        (uu____72537, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72529  in
    let uu____72589 =
      let uu____72592 =
        let uu____72593 =
          let uu____72601 =
            let uu____72602 =
              let uu____72613 =
                let uu____72614 =
                  let uu____72619 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72619)  in
                FStar_SMTEncoding_Util.mkImp uu____72614  in
              ([[typing_pred]], [xx], uu____72613)  in
            let uu____72646 =
              let uu____72661 = FStar_TypeChecker_Env.get_range env  in
              let uu____72662 = mkForall_fuel1 env  in
              uu____72662 uu____72661  in
            uu____72646 uu____72602  in
          (uu____72601, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72593  in
      [uu____72592]  in
    uu____72528 :: uu____72589  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72709 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72709]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72739 =
      let uu____72740 =
        let uu____72748 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72748, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72740  in
    [uu____72739]  in
  let mk_and_interp env conj uu____72771 =
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
    let uu____72800 =
      let uu____72801 =
        let uu____72809 =
          let uu____72810 = FStar_TypeChecker_Env.get_range env  in
          let uu____72811 =
            let uu____72822 =
              let uu____72823 =
                let uu____72828 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72828, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72823  in
            ([[l_and_a_b]], [aa; bb], uu____72822)  in
          FStar_SMTEncoding_Term.mkForall uu____72810 uu____72811  in
        (uu____72809, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72801  in
    [uu____72800]  in
  let mk_or_interp env disj uu____72883 =
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
    let uu____72912 =
      let uu____72913 =
        let uu____72921 =
          let uu____72922 = FStar_TypeChecker_Env.get_range env  in
          let uu____72923 =
            let uu____72934 =
              let uu____72935 =
                let uu____72940 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72940, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72935  in
            ([[l_or_a_b]], [aa; bb], uu____72934)  in
          FStar_SMTEncoding_Term.mkForall uu____72922 uu____72923  in
        (uu____72921, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72913  in
    [uu____72912]  in
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
    let uu____73018 =
      let uu____73019 =
        let uu____73027 =
          let uu____73028 = FStar_TypeChecker_Env.get_range env  in
          let uu____73029 =
            let uu____73040 =
              let uu____73041 =
                let uu____73046 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73046, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73041  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73040)  in
          FStar_SMTEncoding_Term.mkForall uu____73028 uu____73029  in
        (uu____73027, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73019  in
    [uu____73018]  in
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
    let uu____73136 =
      let uu____73137 =
        let uu____73145 =
          let uu____73146 = FStar_TypeChecker_Env.get_range env  in
          let uu____73147 =
            let uu____73158 =
              let uu____73159 =
                let uu____73164 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73164, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73159  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73158)  in
          FStar_SMTEncoding_Term.mkForall uu____73146 uu____73147  in
        (uu____73145, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73137  in
    [uu____73136]  in
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
    let uu____73264 =
      let uu____73265 =
        let uu____73273 =
          let uu____73274 = FStar_TypeChecker_Env.get_range env  in
          let uu____73275 =
            let uu____73286 =
              let uu____73287 =
                let uu____73292 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73292, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73287  in
            ([[l_imp_a_b]], [aa; bb], uu____73286)  in
          FStar_SMTEncoding_Term.mkForall uu____73274 uu____73275  in
        (uu____73273, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73265  in
    [uu____73264]  in
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
    let uu____73376 =
      let uu____73377 =
        let uu____73385 =
          let uu____73386 = FStar_TypeChecker_Env.get_range env  in
          let uu____73387 =
            let uu____73398 =
              let uu____73399 =
                let uu____73404 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73404, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73399  in
            ([[l_iff_a_b]], [aa; bb], uu____73398)  in
          FStar_SMTEncoding_Term.mkForall uu____73386 uu____73387  in
        (uu____73385, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73377  in
    [uu____73376]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73475 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73475  in
    let uu____73480 =
      let uu____73481 =
        let uu____73489 =
          let uu____73490 = FStar_TypeChecker_Env.get_range env  in
          let uu____73491 =
            let uu____73502 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73502)  in
          FStar_SMTEncoding_Term.mkForall uu____73490 uu____73491  in
        (uu____73489, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73481  in
    [uu____73480]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73555 =
      let uu____73556 =
        let uu____73564 =
          let uu____73565 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73565 range_ty  in
        let uu____73566 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73564, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73566)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73556  in
    [uu____73555]  in
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
        let uu____73612 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73612 x1 t  in
      let uu____73614 = FStar_TypeChecker_Env.get_range env  in
      let uu____73615 =
        let uu____73626 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73626)  in
      FStar_SMTEncoding_Term.mkForall uu____73614 uu____73615  in
    let uu____73651 =
      let uu____73652 =
        let uu____73660 =
          let uu____73661 = FStar_TypeChecker_Env.get_range env  in
          let uu____73662 =
            let uu____73673 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73673)  in
          FStar_SMTEncoding_Term.mkForall uu____73661 uu____73662  in
        (uu____73660,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73652  in
    [uu____73651]  in
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
    let uu____73734 =
      let uu____73735 =
        let uu____73743 =
          let uu____73744 = FStar_TypeChecker_Env.get_range env  in
          let uu____73745 =
            let uu____73761 =
              let uu____73762 =
                let uu____73767 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73768 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73767, uu____73768)  in
              FStar_SMTEncoding_Util.mkAnd uu____73762  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73761)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73744 uu____73745  in
        (uu____73743,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73735  in
    [uu____73734]  in
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
          let uu____74326 =
            FStar_Util.find_opt
              (fun uu____74364  ->
                 match uu____74364 with
                 | (l,uu____74380) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74326 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74423,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74484 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74484 with
        | (form,decls) ->
            let uu____74493 =
              let uu____74496 =
                let uu____74499 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74499]  in
              FStar_All.pipe_right uu____74496
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74493
  
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
              let uu____74558 =
                ((let uu____74562 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74562) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74558
              then
                let arg_sorts =
                  let uu____74574 =
                    let uu____74575 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74575.FStar_Syntax_Syntax.n  in
                  match uu____74574 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74581) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74619  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74626 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74628 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74628 with
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
                    let uu____74660 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74660, env1)
              else
                (let uu____74665 = prims.is lid  in
                 if uu____74665
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74674 = prims.mk lid vname  in
                   match uu____74674 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74698 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74698, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74707 =
                      let uu____74726 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74726 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74754 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74754
                            then
                              let uu____74759 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_74762 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_74762.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_74762.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_74762.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_74762.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_74762.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_74762.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_74762.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_74762.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_74762.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_74762.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_74762.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_74762.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_74762.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_74762.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_74762.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_74762.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_74762.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_74762.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_74762.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_74762.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_74762.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_74762.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_74762.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_74762.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_74762.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_74762.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_74762.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_74762.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_74762.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_74762.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_74762.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_74762.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_74762.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_74762.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_74762.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_74762.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_74762.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_74762.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_74762.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_74762.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_74762.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_74762.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74759
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74785 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74785)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74707 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74891  ->
                                  match uu___639_74891 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74895 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74895 with
                                       | (uu____74928,xxv) ->
                                           let xx =
                                             let uu____74967 =
                                               let uu____74968 =
                                                 let uu____74974 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____74974,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____74968
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____74967
                                              in
                                           let uu____74977 =
                                             let uu____74978 =
                                               let uu____74986 =
                                                 let uu____74987 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____74988 =
                                                   let uu____74999 =
                                                     let uu____75000 =
                                                       let uu____75005 =
                                                         let uu____75006 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75006
                                                          in
                                                       (vapp, uu____75005)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75000
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____74999)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____74987 uu____74988
                                                  in
                                               (uu____74986,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____74978
                                              in
                                           [uu____74977])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75021 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75021 with
                                       | (uu____75054,xxv) ->
                                           let xx =
                                             let uu____75093 =
                                               let uu____75094 =
                                                 let uu____75100 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75100,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75094
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75093
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
                                           let uu____75111 =
                                             let uu____75112 =
                                               let uu____75120 =
                                                 let uu____75121 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75122 =
                                                   let uu____75133 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75133)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75121 uu____75122
                                                  in
                                               (uu____75120,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75112
                                              in
                                           [uu____75111])
                                  | uu____75146 -> []))
                           in
                        let uu____75147 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75147 with
                         | (vars,guards,env',decls1,uu____75172) ->
                             let uu____75185 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75198 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75198, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75202 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75202 with
                                    | (g,ds) ->
                                        let uu____75215 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75215,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75185 with
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
                                  let should_thunk uu____75238 =
                                    let is_type1 t =
                                      let uu____75246 =
                                        let uu____75247 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75247.FStar_Syntax_Syntax.n  in
                                      match uu____75246 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75251 -> true
                                      | uu____75253 -> false  in
                                    let is_squash1 t =
                                      let uu____75262 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75262 with
                                      | (head1,uu____75281) ->
                                          let uu____75306 =
                                            let uu____75307 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75307.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75306 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75312;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75313;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75315;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75316;_};_},uu____75317)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75325 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75330 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75330))
                                       &&
                                       (let uu____75336 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75336))
                                      &&
                                      (let uu____75339 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75339)
                                     in
                                  let uu____75341 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75400 -> (false, vars)  in
                                  (match uu____75341 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75450 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75450 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75482 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75491 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75491
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75502 ->
                                                  let uu____75511 =
                                                    let uu____75519 =
                                                      get_vtok ()  in
                                                    (uu____75519, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75511
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75526 =
                                                let uu____75534 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75534)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75526
                                               in
                                            let uu____75548 =
                                              let vname_decl =
                                                let uu____75556 =
                                                  let uu____75568 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75568,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75556
                                                 in
                                              let uu____75579 =
                                                let env2 =
                                                  let uu___1026_75585 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_75585.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75586 =
                                                  let uu____75588 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75588
                                                   in
                                                if uu____75586
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75579 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75605 =
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
                                                        let uu____75631 =
                                                          let uu____75634 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75634
                                                           in
                                                        let uu____75641 =
                                                          let uu____75642 =
                                                            let uu____75645 =
                                                              let uu____75646
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75646
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75650  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75650)
                                                              uu____75645
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75642
                                                           in
                                                        (uu____75631,
                                                          uu____75641)
                                                    | uu____75653 when
                                                        thunked ->
                                                        let uu____75664 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75664
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75679
                                                                 =
                                                                 let uu____75687
                                                                   =
                                                                   let uu____75690
                                                                    =
                                                                    let uu____75693
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75693]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75690
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75687)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75679
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75701
                                                               =
                                                               let uu____75709
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75709,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75701
                                                              in
                                                           let uu____75714 =
                                                             let uu____75717
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75717
                                                              in
                                                           (uu____75714,
                                                             env1))
                                                    | uu____75726 ->
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
                                                          let uu____75750 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75751 =
                                                            let uu____75762 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75762)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75750
                                                            uu____75751
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75772 =
                                                            let uu____75780 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75780,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75772
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
                                                            let uu____75791 =
                                                              let uu____75792
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75792]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75791
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75819 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75820 =
                                                              let uu____75831
                                                                =
                                                                let uu____75832
                                                                  =
                                                                  let uu____75837
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75838
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75837,
                                                                    uu____75838)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75832
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75831)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75819
                                                              uu____75820
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75867 =
                                                          let uu____75870 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75870
                                                           in
                                                        (uu____75867, env1)
                                                     in
                                                  (match uu____75605 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75891 =
                                                         let uu____75894 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75894
                                                           tok_decl
                                                          in
                                                       (uu____75891, env2))
                                               in
                                            (match uu____75548 with
                                             | (decls2,env2) ->
                                                 let uu____75913 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75923 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75923 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75938 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75938, decls)
                                                    in
                                                 (match uu____75913 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____75953 =
                                                          let uu____75961 =
                                                            let uu____75962 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75963 =
                                                              let uu____75974
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____75974)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75962
                                                              uu____75963
                                                             in
                                                          (uu____75961,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____75953
                                                         in
                                                      let freshness =
                                                        let uu____75990 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____75990
                                                        then
                                                          let uu____75998 =
                                                            let uu____75999 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76000 =
                                                              let uu____76013
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76020
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76013,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76020)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____75999
                                                              uu____76000
                                                             in
                                                          let uu____76026 =
                                                            let uu____76029 =
                                                              let uu____76030
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76030
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76029]  in
                                                          uu____75998 ::
                                                            uu____76026
                                                        else []  in
                                                      let g =
                                                        let uu____76036 =
                                                          let uu____76039 =
                                                            let uu____76042 =
                                                              let uu____76045
                                                                =
                                                                let uu____76048
                                                                  =
                                                                  let uu____76051
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76051
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76048
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76045
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76042
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76039
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76036
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
          let uu____76091 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76091 with
          | FStar_Pervasives_Native.None  ->
              let uu____76102 = encode_free_var false env x t t_norm []  in
              (match uu____76102 with
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
            let uu____76165 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76165 with
            | (decls,env1) ->
                let uu____76176 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76176
                then
                  let uu____76183 =
                    let uu____76184 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76184  in
                  (uu____76183, env1)
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
             (fun uu____76240  ->
                fun lb  ->
                  match uu____76240 with
                  | (decls,env1) ->
                      let uu____76260 =
                        let uu____76265 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76265
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76260 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76294 = FStar_Syntax_Util.head_and_args t  in
    match uu____76294 with
    | (hd1,args) ->
        let uu____76338 =
          let uu____76339 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76339.FStar_Syntax_Syntax.n  in
        (match uu____76338 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76345,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76369 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76380 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_76388 = en  in
    let uu____76389 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_76388.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_76388.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_76388.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_76388.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_76388.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_76388.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_76388.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_76388.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_76388.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_76388.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76389
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76419  ->
      fun quals  ->
        match uu____76419 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76524 = FStar_Util.first_N nbinders formals  in
              match uu____76524 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76621  ->
                         fun uu____76622  ->
                           match (uu____76621, uu____76622) with
                           | ((formal,uu____76648),(binder,uu____76650)) ->
                               let uu____76671 =
                                 let uu____76678 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76678)  in
                               FStar_Syntax_Syntax.NT uu____76671) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76692 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76733  ->
                              match uu____76733 with
                              | (x,i) ->
                                  let uu____76752 =
                                    let uu___1139_76753 = x  in
                                    let uu____76754 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_76753.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_76753.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76754
                                    }  in
                                  (uu____76752, i)))
                       in
                    FStar_All.pipe_right uu____76692
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76778 =
                      let uu____76783 = FStar_Syntax_Subst.compress body  in
                      let uu____76784 =
                        let uu____76785 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76785
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76783
                        uu____76784
                       in
                    uu____76778 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_76834 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_76834.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_76834.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_76834.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_76834.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_76834.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_76834.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_76834.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_76834.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_76834.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_76834.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_76834.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_76834.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_76834.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_76834.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_76834.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_76834.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_76834.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_76834.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_76834.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_76834.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_76834.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_76834.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_76834.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_76834.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_76834.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_76834.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_76834.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_76834.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_76834.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_76834.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_76834.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_76834.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_76834.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_76834.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_76834.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_76834.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_76834.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_76834.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_76834.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_76834.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_76834.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_76834.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76906  ->
                       fun uu____76907  ->
                         match (uu____76906, uu____76907) with
                         | ((x,uu____76933),(b,uu____76935)) ->
                             let uu____76956 =
                               let uu____76963 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____76963)  in
                             FStar_Syntax_Syntax.NT uu____76956) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____76988 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____76988
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77017 ->
                    let uu____77024 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77024
                | uu____77025 when Prims.op_Negation norm1 ->
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
                | uu____77028 ->
                    let uu____77029 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77029)
                 in
              let aux t1 e1 =
                let uu____77071 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77071 with
                | (binders,body,lopt) ->
                    let uu____77103 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77119 -> arrow_formals_comp_norm false t1  in
                    (match uu____77103 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77153 =
                           if nformals < nbinders
                           then
                             let uu____77187 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77187 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77267 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77267)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77297 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77297 with
                                | (binders1,body1) ->
                                    let uu____77350 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77350))
                             else
                               (let uu____77363 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77363))
                            in
                         (match uu____77153 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77423 = aux t e  in
              match uu____77423 with
              | (binders,body,comp) ->
                  let uu____77469 =
                    let uu____77480 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77480
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77495 = aux comp1 body1  in
                      match uu____77495 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77469 with
                   | (binders1,body1,comp1) ->
                       let uu____77578 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77578, comp1))
               in
            (try
               (fun uu___1216_77605  ->
                  match () with
                  | () ->
                      let uu____77612 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77612
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77628 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77691  ->
                                   fun lb  ->
                                     match uu____77691 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77746 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77746
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77752 =
                                             let uu____77761 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77761
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77752 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77628 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77902;
                                    FStar_Syntax_Syntax.lbeff = uu____77903;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77905;
                                    FStar_Syntax_Syntax.lbpos = uu____77906;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77930 =
                                     let uu____77937 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77937 with
                                     | (tcenv',uu____77953,e_t) ->
                                         let uu____77959 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____77970 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____77959 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_77987 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_77987.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77930 with
                                    | (env',e1,t_norm1) ->
                                        let uu____77997 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____77997 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78017 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78017
                                               then
                                                 let uu____78022 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78025 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78022 uu____78025
                                               else ());
                                              (let uu____78030 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78030 with
                                               | (vars,_guards,env'1,binder_decls,uu____78057)
                                                   ->
                                                   let uu____78070 =
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
                                                         let uu____78087 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78087
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78109 =
                                                          let uu____78110 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78111 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78110 fvb
                                                            uu____78111
                                                           in
                                                        (vars, uu____78109))
                                                      in
                                                   (match uu____78070 with
                                                    | (vars1,app) ->
                                                        let uu____78122 =
                                                          let is_logical =
                                                            let uu____78135 =
                                                              let uu____78136
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78136.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78135
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78142 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78146 =
                                                              let uu____78147
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78147
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78146
                                                              (fun lid  ->
                                                                 let uu____78156
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78156
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78157 =
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
                                                          if uu____78157
                                                          then
                                                            let uu____78173 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78174 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78173,
                                                              uu____78174)
                                                          else
                                                            (let uu____78185
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78185))
                                                           in
                                                        (match uu____78122
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78209
                                                                 =
                                                                 let uu____78217
                                                                   =
                                                                   let uu____78218
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78219
                                                                    =
                                                                    let uu____78230
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78230)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78218
                                                                    uu____78219
                                                                    in
                                                                 let uu____78239
                                                                   =
                                                                   let uu____78240
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78240
                                                                    in
                                                                 (uu____78217,
                                                                   uu____78239,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78209
                                                                in
                                                             let uu____78246
                                                               =
                                                               let uu____78249
                                                                 =
                                                                 let uu____78252
                                                                   =
                                                                   let uu____78255
                                                                    =
                                                                    let uu____78258
                                                                    =
                                                                    let uu____78261
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78261
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78258
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78255
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78252
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78249
                                                                in
                                                             (uu____78246,
                                                               env2)))))))
                               | uu____78270 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78330 =
                                   let uu____78336 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78336,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78330  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78342 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78395  ->
                                         fun fvb  ->
                                           match uu____78395 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78450 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78450
                                                  in
                                               let gtok =
                                                 let uu____78454 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78454
                                                  in
                                               let env4 =
                                                 let uu____78457 =
                                                   let uu____78460 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78466  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78466) uu____78460
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78457
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78342 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78586
                                     t_norm uu____78588 =
                                     match (uu____78586, uu____78588) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78618;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78619;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78621;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78622;_})
                                         ->
                                         let uu____78649 =
                                           let uu____78656 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78656 with
                                           | (tcenv',uu____78672,e_t) ->
                                               let uu____78678 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78689 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78678 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_78706 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_78706.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78649 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78719 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78719
                                                then
                                                  let uu____78724 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78726 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78728 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78724 uu____78726
                                                    uu____78728
                                                else ());
                                               (let uu____78733 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78733 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78760 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78760 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78782 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78782
                                                           then
                                                             let uu____78787
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78789
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78792
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78794
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78787
                                                               uu____78789
                                                               uu____78792
                                                               uu____78794
                                                           else ());
                                                          (let uu____78799 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78799
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78828)
                                                               ->
                                                               let uu____78841
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78854
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78854,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78858
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78858
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78871
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78871,
                                                                    decls0))
                                                                  in
                                                               (match uu____78841
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
                                                                    let uu____78892
                                                                    =
                                                                    let uu____78904
                                                                    =
                                                                    let uu____78907
                                                                    =
                                                                    let uu____78910
                                                                    =
                                                                    let uu____78913
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78913
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78910
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78907
                                                                     in
                                                                    (g,
                                                                    uu____78904,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78892
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
                                                                    let uu____78943
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78943
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
                                                                    let uu____78958
                                                                    =
                                                                    let uu____78961
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____78961
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78958
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____78967
                                                                    =
                                                                    let uu____78970
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____78970
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78967
                                                                     in
                                                                    let uu____78975
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____78975
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____78991
                                                                    =
                                                                    let uu____78999
                                                                    =
                                                                    let uu____79000
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79001
                                                                    =
                                                                    let uu____79017
                                                                    =
                                                                    let uu____79018
                                                                    =
                                                                    let uu____79023
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79023)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79018
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79017)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79000
                                                                    uu____79001
                                                                     in
                                                                    let uu____79037
                                                                    =
                                                                    let uu____79038
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79038
                                                                     in
                                                                    (uu____78999,
                                                                    uu____79037,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____78991
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79045
                                                                    =
                                                                    let uu____79053
                                                                    =
                                                                    let uu____79054
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79055
                                                                    =
                                                                    let uu____79066
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79066)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79054
                                                                    uu____79055
                                                                     in
                                                                    (uu____79053,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79045
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79080
                                                                    =
                                                                    let uu____79088
                                                                    =
                                                                    let uu____79089
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79090
                                                                    =
                                                                    let uu____79101
                                                                    =
                                                                    let uu____79102
                                                                    =
                                                                    let uu____79107
                                                                    =
                                                                    let uu____79108
                                                                    =
                                                                    let uu____79111
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79111
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79108
                                                                     in
                                                                    (gsapp,
                                                                    uu____79107)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79102
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79101)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79089
                                                                    uu____79090
                                                                     in
                                                                    (uu____79088,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79080
                                                                     in
                                                                    let uu____79125
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
                                                                    let uu____79137
                                                                    =
                                                                    let uu____79138
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79138
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79137
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79140
                                                                    =
                                                                    let uu____79148
                                                                    =
                                                                    let uu____79149
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79150
                                                                    =
                                                                    let uu____79161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79161)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79149
                                                                    uu____79150
                                                                     in
                                                                    (uu____79148,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79140
                                                                     in
                                                                    let uu____79174
                                                                    =
                                                                    let uu____79183
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79183
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79198
                                                                    =
                                                                    let uu____79201
                                                                    =
                                                                    let uu____79202
                                                                    =
                                                                    let uu____79210
                                                                    =
                                                                    let uu____79211
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79212
                                                                    =
                                                                    let uu____79223
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79223)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79211
                                                                    uu____79212
                                                                     in
                                                                    (uu____79210,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79202
                                                                     in
                                                                    [uu____79201]
                                                                     in
                                                                    (d3,
                                                                    uu____79198)
                                                                     in
                                                                    match uu____79174
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79125
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79280
                                                                    =
                                                                    let uu____79283
                                                                    =
                                                                    let uu____79286
                                                                    =
                                                                    let uu____79289
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79289
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79286
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79283
                                                                     in
                                                                    let uu____79296
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79280,
                                                                    uu____79296,
                                                                    env02))))))))))
                                      in
                                   let uu____79301 =
                                     let uu____79314 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79377  ->
                                          fun uu____79378  ->
                                            match (uu____79377, uu____79378)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79503 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79503 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79314
                                      in
                                   (match uu____79301 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79570 =
                                          let isDeclFun uu___640_79587 =
                                            match uu___640_79587 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79589 -> true
                                            | uu____79602 -> false  in
                                          let uu____79604 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79604
                                            (fun decls3  ->
                                               let uu____79634 =
                                                 FStar_List.fold_left
                                                   (fun uu____79665  ->
                                                      fun elt  ->
                                                        match uu____79665
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79706 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79706
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79734
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79734
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
                                                                    let uu___1459_79772
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_79772.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_79772.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_79772.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79634 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79804 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79804, elts, rest))
                                           in
                                        (match uu____79570 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79833 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79839  ->
                                        match uu___641_79839 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79842 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79850 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79850)))
                                in
                             if uu____79833
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_79872  ->
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
                   let uu____79911 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79911
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79930 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79930, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____79986 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____79986 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____79992 = encode_sigelt' env se  in
      match uu____79992 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80004 =
                  let uu____80007 =
                    let uu____80008 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80008  in
                  [uu____80007]  in
                FStar_All.pipe_right uu____80004
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80013 ->
                let uu____80014 =
                  let uu____80017 =
                    let uu____80020 =
                      let uu____80021 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80021  in
                    [uu____80020]  in
                  FStar_All.pipe_right uu____80017
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80028 =
                  let uu____80031 =
                    let uu____80034 =
                      let uu____80037 =
                        let uu____80038 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80038  in
                      [uu____80037]  in
                    FStar_All.pipe_right uu____80034
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80031  in
                FStar_List.append uu____80014 uu____80028
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80052 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80052
       then
         let uu____80057 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80057
       else ());
      (let is_opaque_to_smt t =
         let uu____80069 =
           let uu____80070 = FStar_Syntax_Subst.compress t  in
           uu____80070.FStar_Syntax_Syntax.n  in
         match uu____80069 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80075)) -> s = "opaque_to_smt"
         | uu____80080 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80089 =
           let uu____80090 = FStar_Syntax_Subst.compress t  in
           uu____80090.FStar_Syntax_Syntax.n  in
         match uu____80089 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80095)) -> s = "uninterpreted_by_smt"
         | uu____80100 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80106 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80112 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80124 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80125 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80126 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80139 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80141 =
             let uu____80143 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80143  in
           if uu____80141
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80172 ->
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
                let uu____80204 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80204 with
                | (formals,uu____80224) ->
                    let arity = FStar_List.length formals  in
                    let uu____80248 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80248 with
                     | (aname,atok,env2) ->
                         let uu____80270 =
                           let uu____80275 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____80275 env2
                            in
                         (match uu____80270 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80287 =
                                  let uu____80288 =
                                    let uu____80300 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80320  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80300,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80288
                                   in
                                [uu____80287;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80337 =
                                let aux uu____80383 uu____80384 =
                                  match (uu____80383, uu____80384) with
                                  | ((bv,uu____80428),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80460 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80460 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80483 =
                                             let uu____80486 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80486 :: acc_sorts  in
                                           (env4, uu____80483, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80337 with
                               | (uu____80518,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80534 =
                                       let uu____80542 =
                                         let uu____80543 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80544 =
                                           let uu____80555 =
                                             let uu____80556 =
                                               let uu____80561 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80561)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80556
                                              in
                                           ([[app]], xs_sorts, uu____80555)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80543 uu____80544
                                          in
                                       (uu____80542,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80534
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80576 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80576
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80579 =
                                       let uu____80587 =
                                         let uu____80588 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80589 =
                                           let uu____80600 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80600)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80588 uu____80589
                                          in
                                       (uu____80587,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80579
                                      in
                                   let uu____80613 =
                                     let uu____80616 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80616  in
                                   (env2, uu____80613))))
                 in
              let uu____80625 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80625 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80651,uu____80652)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80653 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80653 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80675,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80682 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80688  ->
                       match uu___642_80688 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80691 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80697 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80700 -> false))
                in
             Prims.op_Negation uu____80682  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80710 =
                let uu____80715 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80715 env fv t quals  in
              match uu____80710 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80729 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80729  in
                  let uu____80732 =
                    let uu____80733 =
                      let uu____80736 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80736
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80733  in
                  (uu____80732, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80746 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80746 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_80758 = env  in
                  let uu____80759 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_80758.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_80758.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_80758.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80759;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_80758.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_80758.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_80758.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_80758.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_80758.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_80758.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_80758.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____80761 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80761 with
                 | (f3,decls) ->
                     let g =
                       let uu____80775 =
                         let uu____80778 =
                           let uu____80779 =
                             let uu____80787 =
                               let uu____80788 =
                                 let uu____80790 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80790
                                  in
                               FStar_Pervasives_Native.Some uu____80788  in
                             let uu____80794 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80787, uu____80794)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80779  in
                         [uu____80778]  in
                       FStar_All.pipe_right uu____80775
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80803) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80817 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80839 =
                        let uu____80842 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80842.FStar_Syntax_Syntax.fv_name  in
                      uu____80839.FStar_Syntax_Syntax.v  in
                    let uu____80843 =
                      let uu____80845 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80845  in
                    if uu____80843
                    then
                      let val_decl =
                        let uu___1629_80877 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_80877.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_80877.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_80877.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80878 = encode_sigelt' env1 val_decl  in
                      match uu____80878 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80817 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80914,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80916;
                           FStar_Syntax_Syntax.lbtyp = uu____80917;
                           FStar_Syntax_Syntax.lbeff = uu____80918;
                           FStar_Syntax_Syntax.lbdef = uu____80919;
                           FStar_Syntax_Syntax.lbattrs = uu____80920;
                           FStar_Syntax_Syntax.lbpos = uu____80921;_}::[]),uu____80922)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80941 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80941 with
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
                  let uu____80979 =
                    let uu____80982 =
                      let uu____80983 =
                        let uu____80991 =
                          let uu____80992 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____80993 =
                            let uu____81004 =
                              let uu____81005 =
                                let uu____81010 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81010)  in
                              FStar_SMTEncoding_Util.mkEq uu____81005  in
                            ([[b2t_x]], [xx], uu____81004)  in
                          FStar_SMTEncoding_Term.mkForall uu____80992
                            uu____80993
                           in
                        (uu____80991,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____80983  in
                    [uu____80982]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____80979
                   in
                let uu____81048 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81048, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81051,uu____81052) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81062  ->
                   match uu___643_81062 with
                   | FStar_Syntax_Syntax.Discriminator uu____81064 -> true
                   | uu____81066 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81068,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81080 =
                      let uu____81082 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81082.FStar_Ident.idText  in
                    uu____81080 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81089  ->
                      match uu___644_81089 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81092 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81095) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81109  ->
                   match uu___645_81109 with
                   | FStar_Syntax_Syntax.Projector uu____81111 -> true
                   | uu____81117 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81121 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81121 with
            | FStar_Pervasives_Native.Some uu____81128 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_81130 = se  in
                  let uu____81131 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81131;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_81130.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_81130.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_81130.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81134) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81149) ->
           let uu____81158 = encode_sigelts env ses  in
           (match uu____81158 with
            | (g,env1) ->
                let uu____81169 =
                  FStar_List.fold_left
                    (fun uu____81193  ->
                       fun elt  ->
                         match uu____81193 with
                         | (g',inversions) ->
                             let uu____81221 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81244  ->
                                       match uu___646_81244 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81246;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81247;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81248;_}
                                           -> false
                                       | uu____81255 -> true))
                                in
                             (match uu____81221 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_81280 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_81280.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_81280.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_81280.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81169 with
                 | (g',inversions) ->
                     let uu____81299 =
                       FStar_List.fold_left
                         (fun uu____81330  ->
                            fun elt  ->
                              match uu____81330 with
                              | (decls,elts,rest) ->
                                  let uu____81371 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81380  ->
                                            match uu___647_81380 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81382 -> true
                                            | uu____81395 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81371
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81418 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81439  ->
                                               match uu___648_81439 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81441 -> true
                                               | uu____81454 -> false))
                                        in
                                     match uu____81418 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_81485 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_81485.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_81485.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_81485.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81299 with
                      | (decls,elts,rest) ->
                          let uu____81511 =
                            let uu____81512 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81519 =
                              let uu____81522 =
                                let uu____81525 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81525  in
                              FStar_List.append elts uu____81522  in
                            FStar_List.append uu____81512 uu____81519  in
                          (uu____81511, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81536,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81549 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81549 with
             | (usubst,uvs) ->
                 let uu____81569 =
                   let uu____81576 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81577 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81578 =
                     let uu____81579 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81579 k  in
                   (uu____81576, uu____81577, uu____81578)  in
                 (match uu____81569 with
                  | (env1,tps1,k1) ->
                      let uu____81592 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81592 with
                       | (tps2,k2) ->
                           let uu____81600 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81600 with
                            | (uu____81616,k3) ->
                                let uu____81638 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81638 with
                                 | (tps3,env_tps,uu____81650,us) ->
                                     let u_k =
                                       let uu____81653 =
                                         let uu____81654 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81655 =
                                           let uu____81660 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81662 =
                                             let uu____81663 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81663
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81660 uu____81662
                                            in
                                         uu____81655
                                           FStar_Pervasives_Native.None
                                           uu____81654
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81653 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81681) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81687,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81690) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81698,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81705) ->
                                           let uu____81706 =
                                             let uu____81708 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81708
                                              in
                                           failwith uu____81706
                                       | (uu____81712,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81713 =
                                             let uu____81715 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81715
                                              in
                                           failwith uu____81713
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81719,uu____81720) ->
                                           let uu____81729 =
                                             let uu____81731 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81731
                                              in
                                           failwith uu____81729
                                       | (uu____81735,FStar_Syntax_Syntax.U_unif
                                          uu____81736) ->
                                           let uu____81745 =
                                             let uu____81747 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81747
                                              in
                                           failwith uu____81745
                                       | uu____81751 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81764 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81764 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81782 = u_leq_u_k u_tp  in
                                       if uu____81782
                                       then true
                                       else
                                         (let uu____81789 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81789 with
                                          | (formals,uu____81806) ->
                                              let uu____81827 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81827 with
                                               | (uu____81837,uu____81838,uu____81839,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81850 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81850
             then
               let uu____81855 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81855
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81875  ->
                       match uu___649_81875 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81879 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81892 = c  in
                 match uu____81892 with
                 | (name,args,uu____81897,uu____81898,uu____81899) ->
                     let uu____81910 =
                       let uu____81911 =
                         let uu____81923 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____81950  ->
                                   match uu____81950 with
                                   | (uu____81959,sort,uu____81961) -> sort))
                            in
                         (name, uu____81923,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81911  in
                     [uu____81910]
               else
                 (let uu____81972 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____81972 c)
                in
             let inversion_axioms tapp vars =
               let uu____81990 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____81998 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____81998 FStar_Option.isNone))
                  in
               if uu____81990
               then []
               else
                 (let uu____82033 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82033 with
                  | (xxsym,xx) ->
                      let uu____82046 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82085  ->
                                fun l  ->
                                  match uu____82085 with
                                  | (out,decls) ->
                                      let uu____82105 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82105 with
                                       | (uu____82116,data_t) ->
                                           let uu____82118 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82118 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82162 =
                                                    let uu____82163 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82163.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82162 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82166,indices)
                                                      -> indices
                                                  | uu____82192 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82222  ->
                                                            match uu____82222
                                                            with
                                                            | (x,uu____82230)
                                                                ->
                                                                let uu____82235
                                                                  =
                                                                  let uu____82236
                                                                    =
                                                                    let uu____82244
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82244,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82236
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82235)
                                                       env)
                                                   in
                                                let uu____82249 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82249 with
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
                                                                  let uu____82284
                                                                    =
                                                                    let uu____82289
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82289,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82284)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82292 =
                                                         let uu____82293 =
                                                           let uu____82298 =
                                                             let uu____82299
                                                               =
                                                               let uu____82304
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82305
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82304,
                                                                 uu____82305)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82299
                                                              in
                                                           (out, uu____82298)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82293
                                                          in
                                                       (uu____82292,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82046 with
                       | (data_ax,decls) ->
                           let uu____82320 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82320 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82337 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82337 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82344 =
                                    let uu____82352 =
                                      let uu____82353 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82354 =
                                        let uu____82365 =
                                          let uu____82366 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82368 =
                                            let uu____82371 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82371 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82366 uu____82368
                                           in
                                        let uu____82373 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82365,
                                          uu____82373)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82353 uu____82354
                                       in
                                    let uu____82382 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82352,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82382)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82344
                                   in
                                let uu____82388 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82388)))
                in
             let uu____82395 =
               let uu____82400 =
                 let uu____82401 = FStar_Syntax_Subst.compress k  in
                 uu____82401.FStar_Syntax_Syntax.n  in
               match uu____82400 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____82436 -> (tps, k)  in
             match uu____82395 with
             | (formals,res) ->
                 let uu____82443 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____82443 with
                  | (formals1,res1) ->
                      let uu____82454 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____82454 with
                       | (vars,guards,env',binder_decls,uu____82479) ->
                           let arity = FStar_List.length vars  in
                           let uu____82493 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____82493 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____82519 =
                                    let uu____82527 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____82527)  in
                                  FStar_SMTEncoding_Util.mkApp uu____82519
                                   in
                                let uu____82533 =
                                  let tname_decl =
                                    let uu____82543 =
                                      let uu____82544 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____82563 =
                                                  let uu____82565 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____82565
                                                   in
                                                let uu____82567 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____82563, uu____82567,
                                                  false)))
                                         in
                                      let uu____82571 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____82544,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____82571, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____82543
                                     in
                                  let uu____82579 =
                                    match vars with
                                    | [] ->
                                        let uu____82592 =
                                          let uu____82593 =
                                            let uu____82596 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _82602  ->
                                                 FStar_Pervasives_Native.Some
                                                   _82602) uu____82596
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____82593
                                           in
                                        ([], uu____82592)
                                    | uu____82605 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____82615 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____82615
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____82631 =
                                            let uu____82639 =
                                              let uu____82640 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____82641 =
                                                let uu____82657 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____82657)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____82640 uu____82641
                                               in
                                            (uu____82639,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____82631
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____82579 with
                                  | (tok_decls,env2) ->
                                      let uu____82684 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____82684
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____82533 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____82712 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____82712 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____82734 =
                                                 let uu____82735 =
                                                   let uu____82743 =
                                                     let uu____82744 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____82744
                                                      in
                                                   (uu____82743,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____82735
                                                  in
                                               [uu____82734]
                                             else []  in
                                           let uu____82752 =
                                             let uu____82755 =
                                               let uu____82758 =
                                                 let uu____82761 =
                                                   let uu____82762 =
                                                     let uu____82770 =
                                                       let uu____82771 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____82772 =
                                                         let uu____82783 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____82783)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____82771
                                                         uu____82772
                                                        in
                                                     (uu____82770,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____82762
                                                    in
                                                 [uu____82761]  in
                                               FStar_List.append karr
                                                 uu____82758
                                                in
                                             FStar_All.pipe_right uu____82755
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____82752
                                        in
                                     let aux =
                                       let uu____82802 =
                                         let uu____82805 =
                                           inversion_axioms tapp vars  in
                                         let uu____82808 =
                                           let uu____82811 =
                                             let uu____82814 =
                                               let uu____82815 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____82815 env2
                                                 tapp vars
                                                in
                                             [uu____82814]  in
                                           FStar_All.pipe_right uu____82811
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____82805
                                           uu____82808
                                          in
                                       FStar_List.append kindingAx
                                         uu____82802
                                        in
                                     let g =
                                       let uu____82823 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____82823
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82831,uu____82832,uu____82833,uu____82834,uu____82835)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82843,t,uu____82845,n_tps,uu____82847) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____82857 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____82857 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82905 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82905 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____82929 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____82929 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____82949 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____82949 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83028 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83028,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83035 =
                                   let uu____83036 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83036, true)
                                    in
                                 let uu____83044 =
                                   let uu____83051 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83051
                                    in
                                 FStar_All.pipe_right uu____83035 uu____83044
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
                               let uu____83063 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____83063 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83075::uu____83076 ->
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
                                            let uu____83125 =
                                              let uu____83126 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83126]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83125
                                             in
                                          let uu____83152 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83153 =
                                            let uu____83164 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83164)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83152 uu____83153
                                      | uu____83191 -> tok_typing  in
                                    let uu____83202 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83202 with
                                     | (vars',guards',env'',decls_formals,uu____83227)
                                         ->
                                         let uu____83240 =
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
                                         (match uu____83240 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83270 ->
                                                    let uu____83279 =
                                                      let uu____83280 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83280
                                                       in
                                                    [uu____83279]
                                                 in
                                              let encode_elim uu____83296 =
                                                let uu____83297 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83297 with
                                                | (head1,args) ->
                                                    let uu____83348 =
                                                      let uu____83349 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83349.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83348 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83361;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83362;_},uu____83363)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83369 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83369
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
                                                                  | uu____83432
                                                                    ->
                                                                    let uu____83433
                                                                    =
                                                                    let uu____83439
                                                                    =
                                                                    let uu____83441
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83441
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83439)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83433
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83464
                                                                    =
                                                                    let uu____83466
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83466
                                                                     in
                                                                    if
                                                                    uu____83464
                                                                    then
                                                                    let uu____83488
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83488]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83491
                                                                =
                                                                let uu____83505
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83562
                                                                     ->
                                                                    fun
                                                                    uu____83563
                                                                     ->
                                                                    match 
                                                                    (uu____83562,
                                                                    uu____83563)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83674
                                                                    =
                                                                    let uu____83682
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83682
                                                                     in
                                                                    (match uu____83674
                                                                    with
                                                                    | 
                                                                    (uu____83696,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83707
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83707
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83712
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83712
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
                                                                  uu____83505
                                                                 in
                                                              (match uu____83491
                                                               with
                                                               | (uu____83733,arg_vars,elim_eqns_or_guards,uu____83736)
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
                                                                    let uu____83763
                                                                    =
                                                                    let uu____83771
                                                                    =
                                                                    let uu____83772
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83773
                                                                    =
                                                                    let uu____83784
                                                                    =
                                                                    let uu____83785
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83785
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83787
                                                                    =
                                                                    let uu____83788
                                                                    =
                                                                    let uu____83793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83793)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83788
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83784,
                                                                    uu____83787)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83772
                                                                    uu____83773
                                                                     in
                                                                    (uu____83771,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83763
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83808
                                                                    =
                                                                    let uu____83809
                                                                    =
                                                                    let uu____83815
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83815,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83809
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83808
                                                                     in
                                                                    let uu____83818
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83818
                                                                    then
                                                                    let x =
                                                                    let uu____83822
                                                                    =
                                                                    let uu____83828
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83828,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83822
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83833
                                                                    =
                                                                    let uu____83841
                                                                    =
                                                                    let uu____83842
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83843
                                                                    =
                                                                    let uu____83854
                                                                    =
                                                                    let uu____83859
                                                                    =
                                                                    let uu____83862
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83862]
                                                                     in
                                                                    [uu____83859]
                                                                     in
                                                                    let uu____83867
                                                                    =
                                                                    let uu____83868
                                                                    =
                                                                    let uu____83873
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83875
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83873,
                                                                    uu____83875)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83868
                                                                     in
                                                                    (uu____83854,
                                                                    [x],
                                                                    uu____83867)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83842
                                                                    uu____83843
                                                                     in
                                                                    let uu____83896
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83841,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83896)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83833
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83907
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
                                                                    (let uu____83930
                                                                    =
                                                                    let uu____83931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____83931
                                                                    dapp1  in
                                                                    [uu____83930])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83907
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____83938
                                                                    =
                                                                    let uu____83946
                                                                    =
                                                                    let uu____83947
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83948
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    let uu____83960
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83960
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83962
                                                                    =
                                                                    let uu____83963
                                                                    =
                                                                    let uu____83968
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____83968)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83963
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83959,
                                                                    uu____83962)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83947
                                                                    uu____83948
                                                                     in
                                                                    (uu____83946,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83938)
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
                                                         let uu____83987 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83987
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
                                                                  | uu____84050
                                                                    ->
                                                                    let uu____84051
                                                                    =
                                                                    let uu____84057
                                                                    =
                                                                    let uu____84059
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84059
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84057)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84051
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84082
                                                                    =
                                                                    let uu____84084
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84084
                                                                     in
                                                                    if
                                                                    uu____84082
                                                                    then
                                                                    let uu____84106
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84106]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84109
                                                                =
                                                                let uu____84123
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84180
                                                                     ->
                                                                    fun
                                                                    uu____84181
                                                                     ->
                                                                    match 
                                                                    (uu____84180,
                                                                    uu____84181)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84292
                                                                    =
                                                                    let uu____84300
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84300
                                                                     in
                                                                    (match uu____84292
                                                                    with
                                                                    | 
                                                                    (uu____84314,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84325
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84325
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84330
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84330
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
                                                                  uu____84123
                                                                 in
                                                              (match uu____84109
                                                               with
                                                               | (uu____84351,arg_vars,elim_eqns_or_guards,uu____84354)
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
                                                                    let uu____84381
                                                                    =
                                                                    let uu____84389
                                                                    =
                                                                    let uu____84390
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84391
                                                                    =
                                                                    let uu____84402
                                                                    =
                                                                    let uu____84403
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84403
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84405
                                                                    =
                                                                    let uu____84406
                                                                    =
                                                                    let uu____84411
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84411)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84406
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84402,
                                                                    uu____84405)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84390
                                                                    uu____84391
                                                                     in
                                                                    (uu____84389,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84381
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84426
                                                                    =
                                                                    let uu____84427
                                                                    =
                                                                    let uu____84433
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84433,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84427
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84426
                                                                     in
                                                                    let uu____84436
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84436
                                                                    then
                                                                    let x =
                                                                    let uu____84440
                                                                    =
                                                                    let uu____84446
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84446,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84440
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84451
                                                                    =
                                                                    let uu____84459
                                                                    =
                                                                    let uu____84460
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84461
                                                                    =
                                                                    let uu____84472
                                                                    =
                                                                    let uu____84477
                                                                    =
                                                                    let uu____84480
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84480]
                                                                     in
                                                                    [uu____84477]
                                                                     in
                                                                    let uu____84485
                                                                    =
                                                                    let uu____84486
                                                                    =
                                                                    let uu____84491
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84493
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84491,
                                                                    uu____84493)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84486
                                                                     in
                                                                    (uu____84472,
                                                                    [x],
                                                                    uu____84485)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84460
                                                                    uu____84461
                                                                     in
                                                                    let uu____84514
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84459,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84514)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84451
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84525
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
                                                                    (let uu____84548
                                                                    =
                                                                    let uu____84549
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84549
                                                                    dapp1  in
                                                                    [uu____84548])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84525
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84556
                                                                    =
                                                                    let uu____84564
                                                                    =
                                                                    let uu____84565
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84566
                                                                    =
                                                                    let uu____84577
                                                                    =
                                                                    let uu____84578
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84578
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84580
                                                                    =
                                                                    let uu____84581
                                                                    =
                                                                    let uu____84586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84586)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84581
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84577,
                                                                    uu____84580)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84565
                                                                    uu____84566
                                                                     in
                                                                    (uu____84564,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84556)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84603 ->
                                                         ((let uu____84605 =
                                                             let uu____84611
                                                               =
                                                               let uu____84613
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84615
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84613
                                                                 uu____84615
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84611)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84605);
                                                          ([], [])))
                                                 in
                                              let uu____84623 =
                                                encode_elim ()  in
                                              (match uu____84623 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84649 =
                                                       let uu____84652 =
                                                         let uu____84655 =
                                                           let uu____84658 =
                                                             let uu____84661
                                                               =
                                                               let uu____84664
                                                                 =
                                                                 let uu____84667
                                                                   =
                                                                   let uu____84668
                                                                    =
                                                                    let uu____84680
                                                                    =
                                                                    let uu____84681
                                                                    =
                                                                    let uu____84683
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84683
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84681
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84680)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84668
                                                                    in
                                                                 [uu____84667]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84664
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84661
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84694 =
                                                             let uu____84697
                                                               =
                                                               let uu____84700
                                                                 =
                                                                 let uu____84703
                                                                   =
                                                                   let uu____84706
                                                                    =
                                                                    let uu____84709
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84714
                                                                    =
                                                                    let uu____84717
                                                                    =
                                                                    let uu____84718
                                                                    =
                                                                    let uu____84726
                                                                    =
                                                                    let uu____84727
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84728
                                                                    =
                                                                    let uu____84739
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84739)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84727
                                                                    uu____84728
                                                                     in
                                                                    (uu____84726,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84718
                                                                     in
                                                                    let uu____84752
                                                                    =
                                                                    let uu____84755
                                                                    =
                                                                    let uu____84756
                                                                    =
                                                                    let uu____84764
                                                                    =
                                                                    let uu____84765
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84766
                                                                    =
                                                                    let uu____84777
                                                                    =
                                                                    let uu____84778
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84778
                                                                    vars'  in
                                                                    let uu____84780
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84777,
                                                                    uu____84780)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84765
                                                                    uu____84766
                                                                     in
                                                                    (uu____84764,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84756
                                                                     in
                                                                    [uu____84755]
                                                                     in
                                                                    uu____84717
                                                                    ::
                                                                    uu____84752
                                                                     in
                                                                    uu____84709
                                                                    ::
                                                                    uu____84714
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84706
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84703
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84700
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84697
                                                              in
                                                           FStar_List.append
                                                             uu____84658
                                                             uu____84694
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84655
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84652
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84649
                                                      in
                                                   let uu____84797 =
                                                     let uu____84798 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84798 g
                                                      in
                                                   (uu____84797, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84832  ->
              fun se  ->
                match uu____84832 with
                | (g,env1) ->
                    let uu____84852 = encode_sigelt env1 se  in
                    (match uu____84852 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____84920 =
        match uu____84920 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____84957 ->
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
                 ((let uu____84965 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____84965
                   then
                     let uu____84970 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____84972 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____84974 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____84970 uu____84972 uu____84974
                   else ());
                  (let uu____84979 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____84979 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____84997 =
                         let uu____85005 =
                           let uu____85007 =
                             let uu____85009 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85009
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85007  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85005
                          in
                       (match uu____84997 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85029 = FStar_Options.log_queries ()
                                 in
                              if uu____85029
                              then
                                let uu____85032 =
                                  let uu____85034 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85036 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85038 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85034 uu____85036 uu____85038
                                   in
                                FStar_Pervasives_Native.Some uu____85032
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85054 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85064 =
                                let uu____85067 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85067  in
                              FStar_List.append uu____85054 uu____85064  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85079,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85099 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85099 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85120 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85120 with | (uu____85147,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85200  ->
              match uu____85200 with
              | (l,uu____85209,uu____85210) ->
                  let uu____85213 =
                    let uu____85225 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85225, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85213))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85258  ->
              match uu____85258 with
              | (l,uu____85269,uu____85270) ->
                  let uu____85273 =
                    let uu____85274 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85277  -> FStar_SMTEncoding_Term.Echo _85277)
                      uu____85274
                     in
                  let uu____85278 =
                    let uu____85281 =
                      let uu____85282 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85282  in
                    [uu____85281]  in
                  uu____85273 :: uu____85278))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85300 =
      let uu____85303 =
        let uu____85304 = FStar_Util.psmap_empty ()  in
        let uu____85319 =
          let uu____85328 = FStar_Util.psmap_empty ()  in (uu____85328, [])
           in
        let uu____85335 =
          let uu____85337 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85337 FStar_Ident.string_of_lid  in
        let uu____85339 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85304;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85319;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85335;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85339
        }  in
      [uu____85303]  in
    FStar_ST.op_Colon_Equals last_env uu____85300
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85383 = FStar_ST.op_Bang last_env  in
      match uu____85383 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85411 ->
          let uu___2175_85414 = e  in
          let uu____85415 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_85414.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_85414.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_85414.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_85414.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_85414.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_85414.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_85414.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85415;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_85414.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_85414.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85423 = FStar_ST.op_Bang last_env  in
    match uu____85423 with
    | [] -> failwith "Empty env stack"
    | uu____85450::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85482  ->
    let uu____85483 = FStar_ST.op_Bang last_env  in
    match uu____85483 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85543  ->
    let uu____85544 = FStar_ST.op_Bang last_env  in
    match uu____85544 with
    | [] -> failwith "Popping an empty stack"
    | uu____85571::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85608  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85661  ->
         let uu____85662 = snapshot_env ()  in
         match uu____85662 with
         | (env_depth,()) ->
             let uu____85684 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85684 with
              | (varops_depth,()) ->
                  let uu____85706 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85706 with
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
        (fun uu____85764  ->
           let uu____85765 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85765 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85860 = snapshot msg  in () 
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
        | (uu____85906::uu____85907,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_85915 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_85915.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_85915.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_85915.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____85916 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_85943 = elt  in
        let uu____85944 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_85943.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_85943.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____85944;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_85943.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____85964 =
        let uu____85967 =
          let uu____85968 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____85968  in
        let uu____85969 = open_fact_db_tags env  in uu____85967 ::
          uu____85969
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____85964
  
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
      let uu____85996 = encode_sigelt env se  in
      match uu____85996 with
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
                (let uu____86042 =
                   let uu____86045 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86045
                    in
                 match uu____86042 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86060 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86060
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86090 = FStar_Options.log_queries ()  in
        if uu____86090
        then
          let uu____86095 =
            let uu____86096 =
              let uu____86098 =
                let uu____86100 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86100 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86098  in
            FStar_SMTEncoding_Term.Caption uu____86096  in
          uu____86095 :: decls
        else decls  in
      (let uu____86119 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86119
       then
         let uu____86122 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86122
       else ());
      (let env =
         let uu____86128 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86128 tcenv  in
       let uu____86129 = encode_top_level_facts env se  in
       match uu____86129 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86143 =
               let uu____86146 =
                 let uu____86149 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86149
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86146  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86143)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86182 = FStar_Options.log_queries ()  in
          if uu____86182
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_86202 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_86202.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_86202.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_86202.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_86202.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_86202.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_86202.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_86202.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_86202.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_86202.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_86202.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86207 =
             let uu____86210 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86210
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86207  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86230 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86230
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
          (let uu____86254 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86254
           then
             let uu____86257 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86257
           else ());
          (let env =
             let uu____86265 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86265
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86304  ->
                     fun se  ->
                       match uu____86304 with
                       | (g,env2) ->
                           let uu____86324 = encode_top_level_facts env2 se
                              in
                           (match uu____86324 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86347 =
             encode_signature
               (let uu___2303_86356 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_86356.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_86356.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_86356.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_86356.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_86356.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_86356.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_86356.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_86356.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_86356.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_86356.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86347 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86372 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86372
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86378 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86378))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86406  ->
        match uu____86406 with
        | (decls,fvbs) ->
            ((let uu____86420 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86420
              then ()
              else
                (let uu____86425 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86425
                 then
                   let uu____86428 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86428
                 else ()));
             (let env =
                let uu____86436 = get_env name tcenv  in
                FStar_All.pipe_right uu____86436
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86438 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86438
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86452 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86452
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
        (let uu____86514 =
           let uu____86516 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86516.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86514);
        (let env =
           let uu____86518 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86518 tcenv  in
         let uu____86519 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86558 = aux rest  in
                 (match uu____86558 with
                  | (out,rest1) ->
                      let t =
                        let uu____86586 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86586 with
                        | FStar_Pervasives_Native.Some uu____86589 ->
                            let uu____86590 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86590
                              x.FStar_Syntax_Syntax.sort
                        | uu____86591 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86595 =
                        let uu____86598 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_86601 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_86601.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_86601.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86598 :: out  in
                      (uu____86595, rest1))
             | uu____86606 -> ([], bindings)  in
           let uu____86613 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86613 with
           | (closing,bindings) ->
               let uu____86640 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86640, bindings)
            in
         match uu____86519 with
         | (q1,bindings) ->
             let uu____86671 = encode_env_bindings env bindings  in
             (match uu____86671 with
              | (env_decls,env1) ->
                  ((let uu____86693 =
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
                    if uu____86693
                    then
                      let uu____86700 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86700
                    else ());
                   (let uu____86705 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86705 with
                    | (phi,qdecls) ->
                        let uu____86726 =
                          let uu____86731 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86731 phi
                           in
                        (match uu____86726 with
                         | (labels,phi1) ->
                             let uu____86748 = encode_labels labels  in
                             (match uu____86748 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86784 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86784
                                    then
                                      let uu____86789 =
                                        let uu____86790 =
                                          let uu____86792 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86792
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86790
                                         in
                                      [uu____86789]
                                    else []  in
                                  let query_prelude =
                                    let uu____86800 =
                                      let uu____86801 =
                                        let uu____86802 =
                                          let uu____86805 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86812 =
                                            let uu____86815 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86815
                                             in
                                          FStar_List.append uu____86805
                                            uu____86812
                                           in
                                        FStar_List.append env_decls
                                          uu____86802
                                         in
                                      FStar_All.pipe_right uu____86801
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86800
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86825 =
                                      let uu____86833 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86834 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86833,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86834)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86825
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
  