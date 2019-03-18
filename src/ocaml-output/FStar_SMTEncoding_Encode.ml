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
  let uu____67879 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67879 with
  | (asym,a) ->
      let uu____67890 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67890 with
       | (xsym,x) ->
           let uu____67901 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67901 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____67979 =
                      let uu____67991 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____67991, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____67979  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68011 =
                      let uu____68019 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68019)  in
                    FStar_SMTEncoding_Util.mkApp uu____68011  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68038 =
                    let uu____68041 =
                      let uu____68044 =
                        let uu____68047 =
                          let uu____68048 =
                            let uu____68056 =
                              let uu____68057 =
                                let uu____68068 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68068)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68057
                               in
                            (uu____68056, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68048  in
                        let uu____68080 =
                          let uu____68083 =
                            let uu____68084 =
                              let uu____68092 =
                                let uu____68093 =
                                  let uu____68104 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68104)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68093
                                 in
                              (uu____68092,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68084  in
                          [uu____68083]  in
                        uu____68047 :: uu____68080  in
                      xtok_decl :: uu____68044  in
                    xname_decl :: uu____68041  in
                  (xtok1, (FStar_List.length vars), uu____68038)  in
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
                  let uu____68274 =
                    let uu____68295 =
                      let uu____68314 =
                        let uu____68315 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68315
                         in
                      quant axy uu____68314  in
                    (FStar_Parser_Const.op_Eq, uu____68295)  in
                  let uu____68332 =
                    let uu____68355 =
                      let uu____68376 =
                        let uu____68395 =
                          let uu____68396 =
                            let uu____68397 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68397  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68396
                           in
                        quant axy uu____68395  in
                      (FStar_Parser_Const.op_notEq, uu____68376)  in
                    let uu____68414 =
                      let uu____68437 =
                        let uu____68458 =
                          let uu____68477 =
                            let uu____68478 =
                              let uu____68479 =
                                let uu____68484 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68485 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68484, uu____68485)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68479  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68478
                             in
                          quant xy uu____68477  in
                        (FStar_Parser_Const.op_And, uu____68458)  in
                      let uu____68502 =
                        let uu____68525 =
                          let uu____68546 =
                            let uu____68565 =
                              let uu____68566 =
                                let uu____68567 =
                                  let uu____68572 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68573 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68572, uu____68573)  in
                                FStar_SMTEncoding_Util.mkOr uu____68567  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68566
                               in
                            quant xy uu____68565  in
                          (FStar_Parser_Const.op_Or, uu____68546)  in
                        let uu____68590 =
                          let uu____68613 =
                            let uu____68634 =
                              let uu____68653 =
                                let uu____68654 =
                                  let uu____68655 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68655
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68654
                                 in
                              quant qx uu____68653  in
                            (FStar_Parser_Const.op_Negation, uu____68634)  in
                          let uu____68672 =
                            let uu____68695 =
                              let uu____68716 =
                                let uu____68735 =
                                  let uu____68736 =
                                    let uu____68737 =
                                      let uu____68742 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68743 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68742, uu____68743)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68737
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68736
                                   in
                                quant xy uu____68735  in
                              (FStar_Parser_Const.op_LT, uu____68716)  in
                            let uu____68760 =
                              let uu____68783 =
                                let uu____68804 =
                                  let uu____68823 =
                                    let uu____68824 =
                                      let uu____68825 =
                                        let uu____68830 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68831 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68830, uu____68831)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68825
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68824
                                     in
                                  quant xy uu____68823  in
                                (FStar_Parser_Const.op_LTE, uu____68804)  in
                              let uu____68848 =
                                let uu____68871 =
                                  let uu____68892 =
                                    let uu____68911 =
                                      let uu____68912 =
                                        let uu____68913 =
                                          let uu____68918 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68919 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68918, uu____68919)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68913
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68912
                                       in
                                    quant xy uu____68911  in
                                  (FStar_Parser_Const.op_GT, uu____68892)  in
                                let uu____68936 =
                                  let uu____68959 =
                                    let uu____68980 =
                                      let uu____68999 =
                                        let uu____69000 =
                                          let uu____69001 =
                                            let uu____69006 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69007 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69006, uu____69007)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69001
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69000
                                         in
                                      quant xy uu____68999  in
                                    (FStar_Parser_Const.op_GTE, uu____68980)
                                     in
                                  let uu____69024 =
                                    let uu____69047 =
                                      let uu____69068 =
                                        let uu____69087 =
                                          let uu____69088 =
                                            let uu____69089 =
                                              let uu____69094 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69095 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69094, uu____69095)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69089
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69088
                                           in
                                        quant xy uu____69087  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69068)
                                       in
                                    let uu____69112 =
                                      let uu____69135 =
                                        let uu____69156 =
                                          let uu____69175 =
                                            let uu____69176 =
                                              let uu____69177 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69177
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69176
                                             in
                                          quant qx uu____69175  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69156)
                                         in
                                      let uu____69194 =
                                        let uu____69217 =
                                          let uu____69238 =
                                            let uu____69257 =
                                              let uu____69258 =
                                                let uu____69259 =
                                                  let uu____69264 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69265 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69264, uu____69265)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69259
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69258
                                               in
                                            quant xy uu____69257  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69238)
                                           in
                                        let uu____69282 =
                                          let uu____69305 =
                                            let uu____69326 =
                                              let uu____69345 =
                                                let uu____69346 =
                                                  let uu____69347 =
                                                    let uu____69352 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69353 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69352,
                                                      uu____69353)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69347
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69346
                                                 in
                                              quant xy uu____69345  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69326)
                                             in
                                          let uu____69370 =
                                            let uu____69393 =
                                              let uu____69414 =
                                                let uu____69433 =
                                                  let uu____69434 =
                                                    let uu____69435 =
                                                      let uu____69440 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69441 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69440,
                                                        uu____69441)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69435
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69434
                                                   in
                                                quant xy uu____69433  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69414)
                                               in
                                            let uu____69458 =
                                              let uu____69481 =
                                                let uu____69502 =
                                                  let uu____69521 =
                                                    let uu____69522 =
                                                      let uu____69523 =
                                                        let uu____69528 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69529 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69528,
                                                          uu____69529)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69523
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69522
                                                     in
                                                  quant xy uu____69521  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69502)
                                                 in
                                              let uu____69546 =
                                                let uu____69569 =
                                                  let uu____69590 =
                                                    let uu____69609 =
                                                      let uu____69610 =
                                                        let uu____69611 =
                                                          let uu____69616 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69617 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69616,
                                                            uu____69617)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69611
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69610
                                                       in
                                                    quant xy uu____69609  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69590)
                                                   in
                                                let uu____69634 =
                                                  let uu____69657 =
                                                    let uu____69678 =
                                                      let uu____69697 =
                                                        let uu____69698 =
                                                          let uu____69699 =
                                                            let uu____69704 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69705 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69704,
                                                              uu____69705)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69699
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69698
                                                         in
                                                      quant xy uu____69697
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69678)
                                                     in
                                                  let uu____69722 =
                                                    let uu____69745 =
                                                      let uu____69766 =
                                                        let uu____69785 =
                                                          let uu____69786 =
                                                            let uu____69787 =
                                                              let uu____69792
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69793
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69792,
                                                                uu____69793)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69787
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69786
                                                           in
                                                        quant xy uu____69785
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69766)
                                                       in
                                                    let uu____69810 =
                                                      let uu____69833 =
                                                        let uu____69854 =
                                                          let uu____69873 =
                                                            let uu____69874 =
                                                              let uu____69875
                                                                =
                                                                let uu____69880
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69881
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69880,
                                                                  uu____69881)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69875
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69874
                                                             in
                                                          quant xy
                                                            uu____69873
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69854)
                                                         in
                                                      let uu____69898 =
                                                        let uu____69921 =
                                                          let uu____69942 =
                                                            let uu____69961 =
                                                              let uu____69962
                                                                =
                                                                let uu____69963
                                                                  =
                                                                  let uu____69968
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____69969
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____69968,
                                                                    uu____69969)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____69963
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____69962
                                                               in
                                                            quant xy
                                                              uu____69961
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69942)
                                                           in
                                                        let uu____69986 =
                                                          let uu____70009 =
                                                            let uu____70030 =
                                                              let uu____70049
                                                                =
                                                                let uu____70050
                                                                  =
                                                                  let uu____70051
                                                                    =
                                                                    let uu____70056
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70057
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70056,
                                                                    uu____70057)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70051
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70050
                                                                 in
                                                              quant xy
                                                                uu____70049
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70030)
                                                             in
                                                          let uu____70074 =
                                                            let uu____70097 =
                                                              let uu____70118
                                                                =
                                                                let uu____70137
                                                                  =
                                                                  let uu____70138
                                                                    =
                                                                    let uu____70139
                                                                    =
                                                                    let uu____70144
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70145
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70144,
                                                                    uu____70145)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70139
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70138
                                                                   in
                                                                quant xy
                                                                  uu____70137
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70118)
                                                               in
                                                            let uu____70162 =
                                                              let uu____70185
                                                                =
                                                                let uu____70206
                                                                  =
                                                                  let uu____70225
                                                                    =
                                                                    let uu____70226
                                                                    =
                                                                    let uu____70227
                                                                    =
                                                                    let uu____70232
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70233
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70232,
                                                                    uu____70233)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70227
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70226
                                                                     in
                                                                  quant xy
                                                                    uu____70225
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70206)
                                                                 in
                                                              let uu____70250
                                                                =
                                                                let uu____70273
                                                                  =
                                                                  let uu____70294
                                                                    =
                                                                    let uu____70313
                                                                    =
                                                                    let uu____70314
                                                                    =
                                                                    let uu____70315
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70315
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70314
                                                                     in
                                                                    quant qx
                                                                    uu____70313
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70294)
                                                                   in
                                                                [uu____70273]
                                                                 in
                                                              uu____70185 ::
                                                                uu____70250
                                                               in
                                                            uu____70097 ::
                                                              uu____70162
                                                             in
                                                          uu____70009 ::
                                                            uu____70074
                                                           in
                                                        uu____69921 ::
                                                          uu____69986
                                                         in
                                                      uu____69833 ::
                                                        uu____69898
                                                       in
                                                    uu____69745 ::
                                                      uu____69810
                                                     in
                                                  uu____69657 :: uu____69722
                                                   in
                                                uu____69569 :: uu____69634
                                                 in
                                              uu____69481 :: uu____69546  in
                                            uu____69393 :: uu____69458  in
                                          uu____69305 :: uu____69370  in
                                        uu____69217 :: uu____69282  in
                                      uu____69135 :: uu____69194  in
                                    uu____69047 :: uu____69112  in
                                  uu____68959 :: uu____69024  in
                                uu____68871 :: uu____68936  in
                              uu____68783 :: uu____68848  in
                            uu____68695 :: uu____68760  in
                          uu____68613 :: uu____68672  in
                        uu____68525 :: uu____68590  in
                      uu____68437 :: uu____68502  in
                    uu____68355 :: uu____68414  in
                  uu____68274 :: uu____68332  in
                let mk1 l v1 =
                  let uu____70854 =
                    let uu____70866 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____70956  ->
                              match uu____70956 with
                              | (l',uu____70977) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70866
                      (FStar_Option.map
                         (fun uu____71076  ->
                            match uu____71076 with
                            | (uu____71104,b) ->
                                let uu____71138 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71138 v1))
                     in
                  FStar_All.pipe_right uu____70854 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71221  ->
                          match uu____71221 with
                          | (l',uu____71242) -> FStar_Ident.lid_equals l l'))
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
          let uu____71316 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71316 with
          | (xxsym,xx) ->
              let uu____71327 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71327 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71343 =
                     let uu____71351 =
                       let uu____71352 =
                         let uu____71363 =
                           let uu____71364 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71374 =
                             let uu____71385 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71385 :: vars  in
                           uu____71364 :: uu____71374  in
                         let uu____71411 =
                           let uu____71412 =
                             let uu____71417 =
                               let uu____71418 =
                                 let uu____71423 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71423)  in
                               FStar_SMTEncoding_Util.mkEq uu____71418  in
                             (xx_has_type, uu____71417)  in
                           FStar_SMTEncoding_Util.mkImp uu____71412  in
                         ([[xx_has_type]], uu____71363, uu____71411)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71352  in
                     let uu____71436 =
                       let uu____71438 =
                         let uu____71440 =
                           let uu____71442 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71442  in
                         Prims.op_Hat module_name uu____71440  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71438
                        in
                     (uu____71351,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71436)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71343)
  
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
    let uu____71498 =
      let uu____71500 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71500  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71498  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71522 =
      let uu____71523 =
        let uu____71531 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71531, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71523  in
    let uu____71536 =
      let uu____71539 =
        let uu____71540 =
          let uu____71548 =
            let uu____71549 =
              let uu____71560 =
                let uu____71561 =
                  let uu____71566 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71566)  in
                FStar_SMTEncoding_Util.mkImp uu____71561  in
              ([[typing_pred]], [xx], uu____71560)  in
            let uu____71591 =
              let uu____71606 = FStar_TypeChecker_Env.get_range env  in
              let uu____71607 = mkForall_fuel1 env  in
              uu____71607 uu____71606  in
            uu____71591 uu____71549  in
          (uu____71548, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71540  in
      [uu____71539]  in
    uu____71522 :: uu____71536  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71654 =
      let uu____71655 =
        let uu____71663 =
          let uu____71664 = FStar_TypeChecker_Env.get_range env  in
          let uu____71665 =
            let uu____71676 =
              let uu____71681 =
                let uu____71684 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71684]  in
              [uu____71681]  in
            let uu____71689 =
              let uu____71690 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71690 tt  in
            (uu____71676, [bb], uu____71689)  in
          FStar_SMTEncoding_Term.mkForall uu____71664 uu____71665  in
        (uu____71663, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71655  in
    let uu____71715 =
      let uu____71718 =
        let uu____71719 =
          let uu____71727 =
            let uu____71728 =
              let uu____71739 =
                let uu____71740 =
                  let uu____71745 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71745)  in
                FStar_SMTEncoding_Util.mkImp uu____71740  in
              ([[typing_pred]], [xx], uu____71739)  in
            let uu____71772 =
              let uu____71787 = FStar_TypeChecker_Env.get_range env  in
              let uu____71788 = mkForall_fuel1 env  in
              uu____71788 uu____71787  in
            uu____71772 uu____71728  in
          (uu____71727, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71719  in
      [uu____71718]  in
    uu____71654 :: uu____71715  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71831 =
        let uu____71832 =
          let uu____71838 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71838, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71832  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71831  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71852 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71852  in
    let uu____71857 =
      let uu____71858 =
        let uu____71866 =
          let uu____71867 = FStar_TypeChecker_Env.get_range env  in
          let uu____71868 =
            let uu____71879 =
              let uu____71884 =
                let uu____71887 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71887]  in
              [uu____71884]  in
            let uu____71892 =
              let uu____71893 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71893 tt  in
            (uu____71879, [bb], uu____71892)  in
          FStar_SMTEncoding_Term.mkForall uu____71867 uu____71868  in
        (uu____71866, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71858  in
    let uu____71918 =
      let uu____71921 =
        let uu____71922 =
          let uu____71930 =
            let uu____71931 =
              let uu____71942 =
                let uu____71943 =
                  let uu____71948 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71948)  in
                FStar_SMTEncoding_Util.mkImp uu____71943  in
              ([[typing_pred]], [xx], uu____71942)  in
            let uu____71975 =
              let uu____71990 = FStar_TypeChecker_Env.get_range env  in
              let uu____71991 = mkForall_fuel1 env  in
              uu____71991 uu____71990  in
            uu____71975 uu____71931  in
          (uu____71930, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71922  in
      let uu____72013 =
        let uu____72016 =
          let uu____72017 =
            let uu____72025 =
              let uu____72026 =
                let uu____72037 =
                  let uu____72038 =
                    let uu____72043 =
                      let uu____72044 =
                        let uu____72047 =
                          let uu____72050 =
                            let uu____72053 =
                              let uu____72054 =
                                let uu____72059 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72060 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72059, uu____72060)  in
                              FStar_SMTEncoding_Util.mkGT uu____72054  in
                            let uu____72062 =
                              let uu____72065 =
                                let uu____72066 =
                                  let uu____72071 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72072 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72071, uu____72072)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72066  in
                              let uu____72074 =
                                let uu____72077 =
                                  let uu____72078 =
                                    let uu____72083 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72084 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72083, uu____72084)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72078  in
                                [uu____72077]  in
                              uu____72065 :: uu____72074  in
                            uu____72053 :: uu____72062  in
                          typing_pred_y :: uu____72050  in
                        typing_pred :: uu____72047  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72044  in
                    (uu____72043, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72038  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72037)
                 in
              let uu____72117 =
                let uu____72132 = FStar_TypeChecker_Env.get_range env  in
                let uu____72133 = mkForall_fuel1 env  in
                uu____72133 uu____72132  in
              uu____72117 uu____72026  in
            (uu____72025,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72017  in
        [uu____72016]  in
      uu____71921 :: uu____72013  in
    uu____71857 :: uu____71918  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72176 =
        let uu____72177 =
          let uu____72183 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72183, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72177  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72176  in
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
      let uu____72199 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72199  in
    let uu____72204 =
      let uu____72205 =
        let uu____72213 =
          let uu____72214 = FStar_TypeChecker_Env.get_range env  in
          let uu____72215 =
            let uu____72226 =
              let uu____72231 =
                let uu____72234 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72234]  in
              [uu____72231]  in
            let uu____72239 =
              let uu____72240 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72240 tt  in
            (uu____72226, [bb], uu____72239)  in
          FStar_SMTEncoding_Term.mkForall uu____72214 uu____72215  in
        (uu____72213, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72205  in
    let uu____72265 =
      let uu____72268 =
        let uu____72269 =
          let uu____72277 =
            let uu____72278 =
              let uu____72289 =
                let uu____72290 =
                  let uu____72295 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72295)  in
                FStar_SMTEncoding_Util.mkImp uu____72290  in
              ([[typing_pred]], [xx], uu____72289)  in
            let uu____72322 =
              let uu____72337 = FStar_TypeChecker_Env.get_range env  in
              let uu____72338 = mkForall_fuel1 env  in
              uu____72338 uu____72337  in
            uu____72322 uu____72278  in
          (uu____72277, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72269  in
      let uu____72360 =
        let uu____72363 =
          let uu____72364 =
            let uu____72372 =
              let uu____72373 =
                let uu____72384 =
                  let uu____72385 =
                    let uu____72390 =
                      let uu____72391 =
                        let uu____72394 =
                          let uu____72397 =
                            let uu____72400 =
                              let uu____72401 =
                                let uu____72406 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72407 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72406, uu____72407)  in
                              FStar_SMTEncoding_Util.mkGT uu____72401  in
                            let uu____72409 =
                              let uu____72412 =
                                let uu____72413 =
                                  let uu____72418 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72419 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72418, uu____72419)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72413  in
                              let uu____72421 =
                                let uu____72424 =
                                  let uu____72425 =
                                    let uu____72430 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72431 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72430, uu____72431)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72425  in
                                [uu____72424]  in
                              uu____72412 :: uu____72421  in
                            uu____72400 :: uu____72409  in
                          typing_pred_y :: uu____72397  in
                        typing_pred :: uu____72394  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72391  in
                    (uu____72390, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72385  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72384)
                 in
              let uu____72464 =
                let uu____72479 = FStar_TypeChecker_Env.get_range env  in
                let uu____72480 = mkForall_fuel1 env  in
                uu____72480 uu____72479  in
              uu____72464 uu____72373  in
            (uu____72372,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72364  in
        [uu____72363]  in
      uu____72268 :: uu____72360  in
    uu____72204 :: uu____72265  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72527 =
      let uu____72528 =
        let uu____72536 =
          let uu____72537 = FStar_TypeChecker_Env.get_range env  in
          let uu____72538 =
            let uu____72549 =
              let uu____72554 =
                let uu____72557 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72557]  in
              [uu____72554]  in
            let uu____72562 =
              let uu____72563 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72563 tt  in
            (uu____72549, [bb], uu____72562)  in
          FStar_SMTEncoding_Term.mkForall uu____72537 uu____72538  in
        (uu____72536, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72528  in
    let uu____72588 =
      let uu____72591 =
        let uu____72592 =
          let uu____72600 =
            let uu____72601 =
              let uu____72612 =
                let uu____72613 =
                  let uu____72618 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72618)  in
                FStar_SMTEncoding_Util.mkImp uu____72613  in
              ([[typing_pred]], [xx], uu____72612)  in
            let uu____72645 =
              let uu____72660 = FStar_TypeChecker_Env.get_range env  in
              let uu____72661 = mkForall_fuel1 env  in
              uu____72661 uu____72660  in
            uu____72645 uu____72601  in
          (uu____72600, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72592  in
      [uu____72591]  in
    uu____72527 :: uu____72588  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72708 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72708]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72738 =
      let uu____72739 =
        let uu____72747 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72747, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72739  in
    [uu____72738]  in
  let mk_and_interp env conj uu____72770 =
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
    let uu____72799 =
      let uu____72800 =
        let uu____72808 =
          let uu____72809 = FStar_TypeChecker_Env.get_range env  in
          let uu____72810 =
            let uu____72821 =
              let uu____72822 =
                let uu____72827 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72827, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72822  in
            ([[l_and_a_b]], [aa; bb], uu____72821)  in
          FStar_SMTEncoding_Term.mkForall uu____72809 uu____72810  in
        (uu____72808, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72800  in
    [uu____72799]  in
  let mk_or_interp env disj uu____72882 =
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
    let uu____72911 =
      let uu____72912 =
        let uu____72920 =
          let uu____72921 = FStar_TypeChecker_Env.get_range env  in
          let uu____72922 =
            let uu____72933 =
              let uu____72934 =
                let uu____72939 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72939, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72934  in
            ([[l_or_a_b]], [aa; bb], uu____72933)  in
          FStar_SMTEncoding_Term.mkForall uu____72921 uu____72922  in
        (uu____72920, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72912  in
    [uu____72911]  in
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
    let uu____73017 =
      let uu____73018 =
        let uu____73026 =
          let uu____73027 = FStar_TypeChecker_Env.get_range env  in
          let uu____73028 =
            let uu____73039 =
              let uu____73040 =
                let uu____73045 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73045, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73040  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73039)  in
          FStar_SMTEncoding_Term.mkForall uu____73027 uu____73028  in
        (uu____73026, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73018  in
    [uu____73017]  in
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
    let uu____73135 =
      let uu____73136 =
        let uu____73144 =
          let uu____73145 = FStar_TypeChecker_Env.get_range env  in
          let uu____73146 =
            let uu____73157 =
              let uu____73158 =
                let uu____73163 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73163, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73158  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73157)  in
          FStar_SMTEncoding_Term.mkForall uu____73145 uu____73146  in
        (uu____73144, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73136  in
    [uu____73135]  in
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
    let uu____73263 =
      let uu____73264 =
        let uu____73272 =
          let uu____73273 = FStar_TypeChecker_Env.get_range env  in
          let uu____73274 =
            let uu____73285 =
              let uu____73286 =
                let uu____73291 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73291, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73286  in
            ([[l_imp_a_b]], [aa; bb], uu____73285)  in
          FStar_SMTEncoding_Term.mkForall uu____73273 uu____73274  in
        (uu____73272, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73264  in
    [uu____73263]  in
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
    let uu____73375 =
      let uu____73376 =
        let uu____73384 =
          let uu____73385 = FStar_TypeChecker_Env.get_range env  in
          let uu____73386 =
            let uu____73397 =
              let uu____73398 =
                let uu____73403 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73403, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73398  in
            ([[l_iff_a_b]], [aa; bb], uu____73397)  in
          FStar_SMTEncoding_Term.mkForall uu____73385 uu____73386  in
        (uu____73384, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73376  in
    [uu____73375]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73474 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73474  in
    let uu____73479 =
      let uu____73480 =
        let uu____73488 =
          let uu____73489 = FStar_TypeChecker_Env.get_range env  in
          let uu____73490 =
            let uu____73501 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73501)  in
          FStar_SMTEncoding_Term.mkForall uu____73489 uu____73490  in
        (uu____73488, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73480  in
    [uu____73479]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73554 =
      let uu____73555 =
        let uu____73563 =
          let uu____73564 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73564 range_ty  in
        let uu____73565 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73563, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73565)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73555  in
    [uu____73554]  in
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
        let uu____73611 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73611 x1 t  in
      let uu____73613 = FStar_TypeChecker_Env.get_range env  in
      let uu____73614 =
        let uu____73625 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73625)  in
      FStar_SMTEncoding_Term.mkForall uu____73613 uu____73614  in
    let uu____73650 =
      let uu____73651 =
        let uu____73659 =
          let uu____73660 = FStar_TypeChecker_Env.get_range env  in
          let uu____73661 =
            let uu____73672 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73672)  in
          FStar_SMTEncoding_Term.mkForall uu____73660 uu____73661  in
        (uu____73659,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73651  in
    [uu____73650]  in
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
    let uu____73733 =
      let uu____73734 =
        let uu____73742 =
          let uu____73743 = FStar_TypeChecker_Env.get_range env  in
          let uu____73744 =
            let uu____73760 =
              let uu____73761 =
                let uu____73766 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73767 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73766, uu____73767)  in
              FStar_SMTEncoding_Util.mkAnd uu____73761  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73760)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73743 uu____73744  in
        (uu____73742,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73734  in
    [uu____73733]  in
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
          let uu____74325 =
            FStar_Util.find_opt
              (fun uu____74363  ->
                 match uu____74363 with
                 | (l,uu____74379) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74325 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74422,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74483 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74483 with
        | (form,decls) ->
            let uu____74492 =
              let uu____74495 =
                let uu____74498 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74498]  in
              FStar_All.pipe_right uu____74495
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74492
  
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
              let uu____74557 =
                ((let uu____74561 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74561) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74557
              then
                let arg_sorts =
                  let uu____74573 =
                    let uu____74574 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74574.FStar_Syntax_Syntax.n  in
                  match uu____74573 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74580) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74618  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74625 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74627 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74627 with
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
                    let uu____74659 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74659, env1)
              else
                (let uu____74664 = prims.is lid  in
                 if uu____74664
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74673 = prims.mk lid vname  in
                   match uu____74673 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74697 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74697, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74706 =
                      let uu____74725 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74725 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74753 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74753
                            then
                              let uu____74758 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_74761 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_74761.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_74761.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_74761.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_74761.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_74761.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_74761.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_74761.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_74761.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_74761.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_74761.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_74761.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_74761.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_74761.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_74761.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_74761.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_74761.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_74761.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_74761.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_74761.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_74761.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_74761.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_74761.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_74761.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_74761.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_74761.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_74761.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_74761.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_74761.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_74761.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_74761.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_74761.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_74761.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_74761.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_74761.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_74761.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_74761.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_74761.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_74761.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_74761.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_74761.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_74761.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_74761.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74758
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74784 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74784)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74706 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74890  ->
                                  match uu___639_74890 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74894 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74894 with
                                       | (uu____74927,xxv) ->
                                           let xx =
                                             let uu____74966 =
                                               let uu____74967 =
                                                 let uu____74973 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____74973,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____74967
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____74966
                                              in
                                           let uu____74976 =
                                             let uu____74977 =
                                               let uu____74985 =
                                                 let uu____74986 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____74987 =
                                                   let uu____74998 =
                                                     let uu____74999 =
                                                       let uu____75004 =
                                                         let uu____75005 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75005
                                                          in
                                                       (vapp, uu____75004)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____74999
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____74998)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____74986 uu____74987
                                                  in
                                               (uu____74985,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____74977
                                              in
                                           [uu____74976])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75020 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75020 with
                                       | (uu____75053,xxv) ->
                                           let xx =
                                             let uu____75092 =
                                               let uu____75093 =
                                                 let uu____75099 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75099,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75093
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75092
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
                                           let uu____75110 =
                                             let uu____75111 =
                                               let uu____75119 =
                                                 let uu____75120 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75121 =
                                                   let uu____75132 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75132)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75120 uu____75121
                                                  in
                                               (uu____75119,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75111
                                              in
                                           [uu____75110])
                                  | uu____75145 -> []))
                           in
                        let uu____75146 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75146 with
                         | (vars,guards,env',decls1,uu____75171) ->
                             let uu____75184 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75197 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75197, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75201 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75201 with
                                    | (g,ds) ->
                                        let uu____75214 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75214,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75184 with
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
                                  let should_thunk uu____75237 =
                                    let is_type1 t =
                                      let uu____75245 =
                                        let uu____75246 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75246.FStar_Syntax_Syntax.n  in
                                      match uu____75245 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75250 -> true
                                      | uu____75252 -> false  in
                                    let is_squash1 t =
                                      let uu____75261 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75261 with
                                      | (head1,uu____75280) ->
                                          let uu____75305 =
                                            let uu____75306 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75306.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75305 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75311;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75312;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75314;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75315;_};_},uu____75316)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75324 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75329 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75329))
                                       &&
                                       (let uu____75335 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75335))
                                      &&
                                      (let uu____75338 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75338)
                                     in
                                  let uu____75340 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75399 -> (false, vars)  in
                                  (match uu____75340 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75449 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75449 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75481 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75490 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75490
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75501 ->
                                                  let uu____75510 =
                                                    let uu____75518 =
                                                      get_vtok ()  in
                                                    (uu____75518, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75510
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75525 =
                                                let uu____75533 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75533)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75525
                                               in
                                            let uu____75547 =
                                              let vname_decl =
                                                let uu____75555 =
                                                  let uu____75567 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75567,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75555
                                                 in
                                              let uu____75578 =
                                                let env2 =
                                                  let uu___1026_75584 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_75584.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75585 =
                                                  let uu____75587 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75587
                                                   in
                                                if uu____75585
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75578 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75604 =
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
                                                        let uu____75630 =
                                                          let uu____75633 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75633
                                                           in
                                                        let uu____75640 =
                                                          let uu____75641 =
                                                            let uu____75644 =
                                                              let uu____75645
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75645
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75649  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75649)
                                                              uu____75644
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75641
                                                           in
                                                        (uu____75630,
                                                          uu____75640)
                                                    | uu____75652 when
                                                        thunked ->
                                                        let uu____75663 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75663
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75678
                                                                 =
                                                                 let uu____75686
                                                                   =
                                                                   let uu____75689
                                                                    =
                                                                    let uu____75692
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75692]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75689
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75686)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75678
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75700
                                                               =
                                                               let uu____75708
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75708,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75700
                                                              in
                                                           let uu____75713 =
                                                             let uu____75716
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75716
                                                              in
                                                           (uu____75713,
                                                             env1))
                                                    | uu____75725 ->
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
                                                          let uu____75749 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75750 =
                                                            let uu____75761 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75761)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75749
                                                            uu____75750
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75771 =
                                                            let uu____75779 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75779,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75771
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
                                                            let uu____75790 =
                                                              let uu____75791
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75791]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75790
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75818 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75819 =
                                                              let uu____75830
                                                                =
                                                                let uu____75831
                                                                  =
                                                                  let uu____75836
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75837
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75836,
                                                                    uu____75837)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75831
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75830)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75818
                                                              uu____75819
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75866 =
                                                          let uu____75869 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75869
                                                           in
                                                        (uu____75866, env1)
                                                     in
                                                  (match uu____75604 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75890 =
                                                         let uu____75893 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75893
                                                           tok_decl
                                                          in
                                                       (uu____75890, env2))
                                               in
                                            (match uu____75547 with
                                             | (decls2,env2) ->
                                                 let uu____75912 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75922 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75922 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75937 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75937, decls)
                                                    in
                                                 (match uu____75912 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____75952 =
                                                          let uu____75960 =
                                                            let uu____75961 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75962 =
                                                              let uu____75973
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____75973)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75961
                                                              uu____75962
                                                             in
                                                          (uu____75960,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____75952
                                                         in
                                                      let freshness =
                                                        let uu____75989 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____75989
                                                        then
                                                          let uu____75997 =
                                                            let uu____75998 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75999 =
                                                              let uu____76012
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76019
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76012,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76019)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____75998
                                                              uu____75999
                                                             in
                                                          let uu____76025 =
                                                            let uu____76028 =
                                                              let uu____76029
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76029
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76028]  in
                                                          uu____75997 ::
                                                            uu____76025
                                                        else []  in
                                                      let g =
                                                        let uu____76035 =
                                                          let uu____76038 =
                                                            let uu____76041 =
                                                              let uu____76044
                                                                =
                                                                let uu____76047
                                                                  =
                                                                  let uu____76050
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76050
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76047
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76044
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76041
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76038
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76035
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
          let uu____76090 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76090 with
          | FStar_Pervasives_Native.None  ->
              let uu____76101 = encode_free_var false env x t t_norm []  in
              (match uu____76101 with
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
            let uu____76164 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76164 with
            | (decls,env1) ->
                let uu____76175 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76175
                then
                  let uu____76182 =
                    let uu____76183 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76183  in
                  (uu____76182, env1)
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
             (fun uu____76239  ->
                fun lb  ->
                  match uu____76239 with
                  | (decls,env1) ->
                      let uu____76259 =
                        let uu____76264 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76264
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76259 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76293 = FStar_Syntax_Util.head_and_args t  in
    match uu____76293 with
    | (hd1,args) ->
        let uu____76337 =
          let uu____76338 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76338.FStar_Syntax_Syntax.n  in
        (match uu____76337 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76344,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76368 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76379 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_76387 = en  in
    let uu____76388 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_76387.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_76387.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_76387.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_76387.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_76387.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_76387.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_76387.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_76387.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_76387.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_76387.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76388
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76418  ->
      fun quals  ->
        match uu____76418 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76523 = FStar_Util.first_N nbinders formals  in
              match uu____76523 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76620  ->
                         fun uu____76621  ->
                           match (uu____76620, uu____76621) with
                           | ((formal,uu____76647),(binder,uu____76649)) ->
                               let uu____76670 =
                                 let uu____76677 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76677)  in
                               FStar_Syntax_Syntax.NT uu____76670) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76691 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76732  ->
                              match uu____76732 with
                              | (x,i) ->
                                  let uu____76751 =
                                    let uu___1139_76752 = x  in
                                    let uu____76753 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_76752.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_76752.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76753
                                    }  in
                                  (uu____76751, i)))
                       in
                    FStar_All.pipe_right uu____76691
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76777 =
                      let uu____76782 = FStar_Syntax_Subst.compress body  in
                      let uu____76783 =
                        let uu____76784 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76784
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76782
                        uu____76783
                       in
                    uu____76777 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_76833 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_76833.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_76833.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_76833.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_76833.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_76833.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_76833.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_76833.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_76833.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_76833.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_76833.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_76833.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_76833.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_76833.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_76833.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_76833.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_76833.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_76833.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_76833.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_76833.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_76833.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_76833.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_76833.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_76833.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_76833.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_76833.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_76833.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_76833.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_76833.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_76833.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_76833.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_76833.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_76833.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_76833.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_76833.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_76833.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_76833.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_76833.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_76833.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_76833.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_76833.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_76833.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_76833.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76905  ->
                       fun uu____76906  ->
                         match (uu____76905, uu____76906) with
                         | ((x,uu____76932),(b,uu____76934)) ->
                             let uu____76955 =
                               let uu____76962 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____76962)  in
                             FStar_Syntax_Syntax.NT uu____76955) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____76987 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____76987
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77016 ->
                    let uu____77023 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77023
                | uu____77024 when Prims.op_Negation norm1 ->
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
                | uu____77027 ->
                    let uu____77028 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77028)
                 in
              let aux t1 e1 =
                let uu____77070 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77070 with
                | (binders,body,lopt) ->
                    let uu____77102 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77118 -> arrow_formals_comp_norm false t1  in
                    (match uu____77102 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77152 =
                           if nformals < nbinders
                           then
                             let uu____77186 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77186 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77266 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77266)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77296 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77296 with
                                | (binders1,body1) ->
                                    let uu____77349 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77349))
                             else
                               (let uu____77362 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77362))
                            in
                         (match uu____77152 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77422 = aux t e  in
              match uu____77422 with
              | (binders,body,comp) ->
                  let uu____77468 =
                    let uu____77479 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77479
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77494 = aux comp1 body1  in
                      match uu____77494 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77468 with
                   | (binders1,body1,comp1) ->
                       let uu____77577 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77577, comp1))
               in
            (try
               (fun uu___1216_77604  ->
                  match () with
                  | () ->
                      let uu____77611 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77611
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77627 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77690  ->
                                   fun lb  ->
                                     match uu____77690 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77745 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77745
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77751 =
                                             let uu____77760 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77760
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77751 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77627 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77901;
                                    FStar_Syntax_Syntax.lbeff = uu____77902;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77904;
                                    FStar_Syntax_Syntax.lbpos = uu____77905;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77929 =
                                     let uu____77936 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77936 with
                                     | (tcenv',uu____77952,e_t) ->
                                         let uu____77958 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____77969 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____77958 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_77986 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_77986.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77929 with
                                    | (env',e1,t_norm1) ->
                                        let uu____77996 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____77996 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78016 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78016
                                               then
                                                 let uu____78021 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78024 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78021 uu____78024
                                               else ());
                                              (let uu____78029 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78029 with
                                               | (vars,_guards,env'1,binder_decls,uu____78056)
                                                   ->
                                                   let uu____78069 =
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
                                                         let uu____78086 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78086
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78108 =
                                                          let uu____78109 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78110 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78109 fvb
                                                            uu____78110
                                                           in
                                                        (vars, uu____78108))
                                                      in
                                                   (match uu____78069 with
                                                    | (vars1,app) ->
                                                        let uu____78121 =
                                                          let is_logical =
                                                            let uu____78134 =
                                                              let uu____78135
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78135.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78134
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78141 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78145 =
                                                              let uu____78146
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78146
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78145
                                                              (fun lid  ->
                                                                 let uu____78155
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78155
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78156 =
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
                                                          if uu____78156
                                                          then
                                                            let uu____78172 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78173 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78172,
                                                              uu____78173)
                                                          else
                                                            (let uu____78184
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78184))
                                                           in
                                                        (match uu____78121
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78208
                                                                 =
                                                                 let uu____78216
                                                                   =
                                                                   let uu____78217
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78218
                                                                    =
                                                                    let uu____78229
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78229)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78217
                                                                    uu____78218
                                                                    in
                                                                 let uu____78238
                                                                   =
                                                                   let uu____78239
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78239
                                                                    in
                                                                 (uu____78216,
                                                                   uu____78238,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78208
                                                                in
                                                             let uu____78245
                                                               =
                                                               let uu____78248
                                                                 =
                                                                 let uu____78251
                                                                   =
                                                                   let uu____78254
                                                                    =
                                                                    let uu____78257
                                                                    =
                                                                    let uu____78260
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78260
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78257
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78254
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78251
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78248
                                                                in
                                                             (uu____78245,
                                                               env2)))))))
                               | uu____78269 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78329 =
                                   let uu____78335 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78335,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78329  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78341 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78394  ->
                                         fun fvb  ->
                                           match uu____78394 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78449 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78449
                                                  in
                                               let gtok =
                                                 let uu____78453 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78453
                                                  in
                                               let env4 =
                                                 let uu____78456 =
                                                   let uu____78459 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78465  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78465) uu____78459
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78456
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78341 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78585
                                     t_norm uu____78587 =
                                     match (uu____78585, uu____78587) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78617;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78618;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78620;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78621;_})
                                         ->
                                         let uu____78648 =
                                           let uu____78655 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78655 with
                                           | (tcenv',uu____78671,e_t) ->
                                               let uu____78677 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78688 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78677 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_78705 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_78705.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78648 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78718 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78718
                                                then
                                                  let uu____78723 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78725 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78727 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78723 uu____78725
                                                    uu____78727
                                                else ());
                                               (let uu____78732 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78732 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78759 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78759 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78781 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78781
                                                           then
                                                             let uu____78786
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78788
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78791
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78793
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78786
                                                               uu____78788
                                                               uu____78791
                                                               uu____78793
                                                           else ());
                                                          (let uu____78798 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78798
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78827)
                                                               ->
                                                               let uu____78840
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78853,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78857
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78857
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78870,
                                                                    decls0))
                                                                  in
                                                               (match uu____78840
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
                                                                    let uu____78891
                                                                    =
                                                                    let uu____78903
                                                                    =
                                                                    let uu____78906
                                                                    =
                                                                    let uu____78909
                                                                    =
                                                                    let uu____78912
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78912
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78909
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78906
                                                                     in
                                                                    (g,
                                                                    uu____78903,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78891
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
                                                                    let uu____78942
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78942
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
                                                                    let uu____78957
                                                                    =
                                                                    let uu____78960
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____78960
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78957
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____78966
                                                                    =
                                                                    let uu____78969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____78969
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78966
                                                                     in
                                                                    let uu____78974
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____78974
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____78990
                                                                    =
                                                                    let uu____78998
                                                                    =
                                                                    let uu____78999
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79000
                                                                    =
                                                                    let uu____79016
                                                                    =
                                                                    let uu____79017
                                                                    =
                                                                    let uu____79022
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79022)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79017
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79016)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____78999
                                                                    uu____79000
                                                                     in
                                                                    let uu____79036
                                                                    =
                                                                    let uu____79037
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79037
                                                                     in
                                                                    (uu____78998,
                                                                    uu____79036,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____78990
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79044
                                                                    =
                                                                    let uu____79052
                                                                    =
                                                                    let uu____79053
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79054
                                                                    =
                                                                    let uu____79065
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79065)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79053
                                                                    uu____79054
                                                                     in
                                                                    (uu____79052,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79044
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79079
                                                                    =
                                                                    let uu____79087
                                                                    =
                                                                    let uu____79088
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79089
                                                                    =
                                                                    let uu____79100
                                                                    =
                                                                    let uu____79101
                                                                    =
                                                                    let uu____79106
                                                                    =
                                                                    let uu____79107
                                                                    =
                                                                    let uu____79110
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79110
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79107
                                                                     in
                                                                    (gsapp,
                                                                    uu____79106)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79101
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79100)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79088
                                                                    uu____79089
                                                                     in
                                                                    (uu____79087,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79079
                                                                     in
                                                                    let uu____79124
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
                                                                    let uu____79136
                                                                    =
                                                                    let uu____79137
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79137
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79136
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79139
                                                                    =
                                                                    let uu____79147
                                                                    =
                                                                    let uu____79148
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79149
                                                                    =
                                                                    let uu____79160
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79160)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79148
                                                                    uu____79149
                                                                     in
                                                                    (uu____79147,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79139
                                                                     in
                                                                    let uu____79173
                                                                    =
                                                                    let uu____79182
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79182
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79197
                                                                    =
                                                                    let uu____79200
                                                                    =
                                                                    let uu____79201
                                                                    =
                                                                    let uu____79209
                                                                    =
                                                                    let uu____79210
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79211
                                                                    =
                                                                    let uu____79222
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79222)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79210
                                                                    uu____79211
                                                                     in
                                                                    (uu____79209,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79201
                                                                     in
                                                                    [uu____79200]
                                                                     in
                                                                    (d3,
                                                                    uu____79197)
                                                                     in
                                                                    match uu____79173
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79124
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79279
                                                                    =
                                                                    let uu____79282
                                                                    =
                                                                    let uu____79285
                                                                    =
                                                                    let uu____79288
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79288
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79285
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79282
                                                                     in
                                                                    let uu____79295
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79279,
                                                                    uu____79295,
                                                                    env02))))))))))
                                      in
                                   let uu____79300 =
                                     let uu____79313 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79376  ->
                                          fun uu____79377  ->
                                            match (uu____79376, uu____79377)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79502 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79502 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79313
                                      in
                                   (match uu____79300 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79569 =
                                          let isDeclFun uu___640_79586 =
                                            match uu___640_79586 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79588 -> true
                                            | uu____79601 -> false  in
                                          let uu____79603 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79603
                                            (fun decls3  ->
                                               let uu____79633 =
                                                 FStar_List.fold_left
                                                   (fun uu____79664  ->
                                                      fun elt  ->
                                                        match uu____79664
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79705 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79705
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79733
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79733
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
                                                                    let uu___1459_79771
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_79771.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_79771.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_79771.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79633 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79803 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79803, elts, rest))
                                           in
                                        (match uu____79569 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79832 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79838  ->
                                        match uu___641_79838 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79841 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79849 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79849)))
                                in
                             if uu____79832
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_79871  ->
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
                   let uu____79910 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79910
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79929 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79929, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____79985 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____79985 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____79991 = encode_sigelt' env se  in
      match uu____79991 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80003 =
                  let uu____80006 =
                    let uu____80007 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80007  in
                  [uu____80006]  in
                FStar_All.pipe_right uu____80003
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80012 ->
                let uu____80013 =
                  let uu____80016 =
                    let uu____80019 =
                      let uu____80020 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80020  in
                    [uu____80019]  in
                  FStar_All.pipe_right uu____80016
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80027 =
                  let uu____80030 =
                    let uu____80033 =
                      let uu____80036 =
                        let uu____80037 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80037  in
                      [uu____80036]  in
                    FStar_All.pipe_right uu____80033
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80030  in
                FStar_List.append uu____80013 uu____80027
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80051 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80051
       then
         let uu____80056 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80056
       else ());
      (let is_opaque_to_smt t =
         let uu____80068 =
           let uu____80069 = FStar_Syntax_Subst.compress t  in
           uu____80069.FStar_Syntax_Syntax.n  in
         match uu____80068 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80074)) -> s = "opaque_to_smt"
         | uu____80079 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80088 =
           let uu____80089 = FStar_Syntax_Subst.compress t  in
           uu____80089.FStar_Syntax_Syntax.n  in
         match uu____80088 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80094)) -> s = "uninterpreted_by_smt"
         | uu____80099 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80105 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80111 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80123 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80124 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80125 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80138 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80140 =
             let uu____80142 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80142  in
           if uu____80140
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80171 ->
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
                let uu____80203 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80203 with
                | (formals,uu____80223) ->
                    let arity = FStar_List.length formals  in
                    let uu____80247 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80247 with
                     | (aname,atok,env2) ->
                         let uu____80269 =
                           let uu____80274 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____80274 env2
                            in
                         (match uu____80269 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80286 =
                                  let uu____80287 =
                                    let uu____80299 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80319  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80299,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80287
                                   in
                                [uu____80286;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80336 =
                                let aux uu____80382 uu____80383 =
                                  match (uu____80382, uu____80383) with
                                  | ((bv,uu____80427),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80459 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80459 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80482 =
                                             let uu____80485 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80485 :: acc_sorts  in
                                           (env4, uu____80482, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80336 with
                               | (uu____80517,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80533 =
                                       let uu____80541 =
                                         let uu____80542 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80543 =
                                           let uu____80554 =
                                             let uu____80555 =
                                               let uu____80560 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80560)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80555
                                              in
                                           ([[app]], xs_sorts, uu____80554)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80542 uu____80543
                                          in
                                       (uu____80541,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80533
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80575 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80575
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80578 =
                                       let uu____80586 =
                                         let uu____80587 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80588 =
                                           let uu____80599 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80599)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80587 uu____80588
                                          in
                                       (uu____80586,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80578
                                      in
                                   let uu____80612 =
                                     let uu____80615 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80615  in
                                   (env2, uu____80612))))
                 in
              let uu____80624 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80624 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80650,uu____80651)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80652 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80652 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80674,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80681 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80687  ->
                       match uu___642_80687 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80690 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80696 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80699 -> false))
                in
             Prims.op_Negation uu____80681  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80709 =
                let uu____80714 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80714 env fv t quals  in
              match uu____80709 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80728 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80728  in
                  let uu____80731 =
                    let uu____80732 =
                      let uu____80735 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80735
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80732  in
                  (uu____80731, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80745 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80745 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_80757 = env  in
                  let uu____80758 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_80757.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_80757.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_80757.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80758;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_80757.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_80757.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_80757.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_80757.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_80757.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_80757.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_80757.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____80760 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80760 with
                 | (f3,decls) ->
                     let g =
                       let uu____80774 =
                         let uu____80777 =
                           let uu____80778 =
                             let uu____80786 =
                               let uu____80787 =
                                 let uu____80789 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80789
                                  in
                               FStar_Pervasives_Native.Some uu____80787  in
                             let uu____80793 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80786, uu____80793)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80778  in
                         [uu____80777]  in
                       FStar_All.pipe_right uu____80774
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80802) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80816 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80838 =
                        let uu____80841 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80841.FStar_Syntax_Syntax.fv_name  in
                      uu____80838.FStar_Syntax_Syntax.v  in
                    let uu____80842 =
                      let uu____80844 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80844  in
                    if uu____80842
                    then
                      let val_decl =
                        let uu___1629_80876 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_80876.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_80876.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_80876.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80877 = encode_sigelt' env1 val_decl  in
                      match uu____80877 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80816 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80913,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80915;
                           FStar_Syntax_Syntax.lbtyp = uu____80916;
                           FStar_Syntax_Syntax.lbeff = uu____80917;
                           FStar_Syntax_Syntax.lbdef = uu____80918;
                           FStar_Syntax_Syntax.lbattrs = uu____80919;
                           FStar_Syntax_Syntax.lbpos = uu____80920;_}::[]),uu____80921)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80940 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80940 with
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
                  let uu____80978 =
                    let uu____80981 =
                      let uu____80982 =
                        let uu____80990 =
                          let uu____80991 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____80992 =
                            let uu____81003 =
                              let uu____81004 =
                                let uu____81009 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81009)  in
                              FStar_SMTEncoding_Util.mkEq uu____81004  in
                            ([[b2t_x]], [xx], uu____81003)  in
                          FStar_SMTEncoding_Term.mkForall uu____80991
                            uu____80992
                           in
                        (uu____80990,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____80982  in
                    [uu____80981]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____80978
                   in
                let uu____81047 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81047, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81050,uu____81051) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81061  ->
                   match uu___643_81061 with
                   | FStar_Syntax_Syntax.Discriminator uu____81063 -> true
                   | uu____81065 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81067,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81079 =
                      let uu____81081 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81081.FStar_Ident.idText  in
                    uu____81079 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81088  ->
                      match uu___644_81088 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81091 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81094) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81108  ->
                   match uu___645_81108 with
                   | FStar_Syntax_Syntax.Projector uu____81110 -> true
                   | uu____81116 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81120 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81120 with
            | FStar_Pervasives_Native.Some uu____81127 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_81129 = se  in
                  let uu____81130 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81130;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_81129.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_81129.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_81129.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81133) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81148) ->
           let uu____81157 = encode_sigelts env ses  in
           (match uu____81157 with
            | (g,env1) ->
                let uu____81168 =
                  FStar_List.fold_left
                    (fun uu____81192  ->
                       fun elt  ->
                         match uu____81192 with
                         | (g',inversions) ->
                             let uu____81220 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81243  ->
                                       match uu___646_81243 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81245;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81246;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81247;_}
                                           -> false
                                       | uu____81254 -> true))
                                in
                             (match uu____81220 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_81279 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_81279.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_81279.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_81279.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81168 with
                 | (g',inversions) ->
                     let uu____81298 =
                       FStar_List.fold_left
                         (fun uu____81329  ->
                            fun elt  ->
                              match uu____81329 with
                              | (decls,elts,rest) ->
                                  let uu____81370 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81379  ->
                                            match uu___647_81379 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81381 -> true
                                            | uu____81394 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81370
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81417 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81438  ->
                                               match uu___648_81438 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81440 -> true
                                               | uu____81453 -> false))
                                        in
                                     match uu____81417 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_81484 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_81484.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_81484.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_81484.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81298 with
                      | (decls,elts,rest) ->
                          let uu____81510 =
                            let uu____81511 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81518 =
                              let uu____81521 =
                                let uu____81524 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81524  in
                              FStar_List.append elts uu____81521  in
                            FStar_List.append uu____81511 uu____81518  in
                          (uu____81510, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81535,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81548 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81548 with
             | (usubst,uvs) ->
                 let uu____81568 =
                   let uu____81575 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81576 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81577 =
                     let uu____81578 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81578 k  in
                   (uu____81575, uu____81576, uu____81577)  in
                 (match uu____81568 with
                  | (env1,tps1,k1) ->
                      let uu____81591 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81591 with
                       | (tps2,k2) ->
                           let uu____81599 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81599 with
                            | (uu____81615,k3) ->
                                let uu____81637 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81637 with
                                 | (tps3,env_tps,uu____81649,us) ->
                                     let u_k =
                                       let uu____81652 =
                                         let uu____81653 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81654 =
                                           let uu____81659 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81661 =
                                             let uu____81662 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81662
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81659 uu____81661
                                            in
                                         uu____81654
                                           FStar_Pervasives_Native.None
                                           uu____81653
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81652 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81680) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81686,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81689) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81697,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81704) ->
                                           let uu____81705 =
                                             let uu____81707 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81707
                                              in
                                           failwith uu____81705
                                       | (uu____81711,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81712 =
                                             let uu____81714 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81714
                                              in
                                           failwith uu____81712
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81718,uu____81719) ->
                                           let uu____81728 =
                                             let uu____81730 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81730
                                              in
                                           failwith uu____81728
                                       | (uu____81734,FStar_Syntax_Syntax.U_unif
                                          uu____81735) ->
                                           let uu____81744 =
                                             let uu____81746 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81746
                                              in
                                           failwith uu____81744
                                       | uu____81750 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81763 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81763 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81781 = u_leq_u_k u_tp  in
                                       if uu____81781
                                       then true
                                       else
                                         (let uu____81788 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81788 with
                                          | (formals,uu____81805) ->
                                              let uu____81826 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81826 with
                                               | (uu____81836,uu____81837,uu____81838,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81849 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81849
             then
               let uu____81854 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81854
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81874  ->
                       match uu___649_81874 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81878 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81891 = c  in
                 match uu____81891 with
                 | (name,args,uu____81896,uu____81897,uu____81898) ->
                     let uu____81909 =
                       let uu____81910 =
                         let uu____81922 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____81949  ->
                                   match uu____81949 with
                                   | (uu____81958,sort,uu____81960) -> sort))
                            in
                         (name, uu____81922,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81910  in
                     [uu____81909]
               else
                 (let uu____81971 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____81971 c)
                in
             let inversion_axioms tapp vars =
               let uu____81989 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____81997 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____81997 FStar_Option.isNone))
                  in
               if uu____81989
               then []
               else
                 (let uu____82032 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82032 with
                  | (xxsym,xx) ->
                      let uu____82045 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82084  ->
                                fun l  ->
                                  match uu____82084 with
                                  | (out,decls) ->
                                      let uu____82104 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82104 with
                                       | (uu____82115,data_t) ->
                                           let uu____82117 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82117 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82161 =
                                                    let uu____82162 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82162.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82161 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82165,indices)
                                                      -> indices
                                                  | uu____82191 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82221  ->
                                                            match uu____82221
                                                            with
                                                            | (x,uu____82229)
                                                                ->
                                                                let uu____82234
                                                                  =
                                                                  let uu____82235
                                                                    =
                                                                    let uu____82243
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82243,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82235
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82234)
                                                       env)
                                                   in
                                                let uu____82248 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82248 with
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
                                                                  let uu____82283
                                                                    =
                                                                    let uu____82288
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82288,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82283)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82291 =
                                                         let uu____82292 =
                                                           let uu____82297 =
                                                             let uu____82298
                                                               =
                                                               let uu____82303
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82304
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82303,
                                                                 uu____82304)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82298
                                                              in
                                                           (out, uu____82297)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82292
                                                          in
                                                       (uu____82291,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82045 with
                       | (data_ax,decls) ->
                           let uu____82319 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82319 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82336 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82336 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82343 =
                                    let uu____82351 =
                                      let uu____82352 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82353 =
                                        let uu____82364 =
                                          let uu____82365 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82367 =
                                            let uu____82370 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82370 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82365 uu____82367
                                           in
                                        let uu____82372 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82364,
                                          uu____82372)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82352 uu____82353
                                       in
                                    let uu____82381 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82351,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82381)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82343
                                   in
                                let uu____82387 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82387)))
                in
             let uu____82394 =
               let uu____82399 =
                 let uu____82400 = FStar_Syntax_Subst.compress k  in
                 uu____82400.FStar_Syntax_Syntax.n  in
               match uu____82399 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____82435 -> (tps, k)  in
             match uu____82394 with
             | (formals,res) ->
                 let uu____82442 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____82442 with
                  | (formals1,res1) ->
                      let uu____82453 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____82453 with
                       | (vars,guards,env',binder_decls,uu____82478) ->
                           let arity = FStar_List.length vars  in
                           let uu____82492 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____82492 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____82518 =
                                    let uu____82526 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____82526)  in
                                  FStar_SMTEncoding_Util.mkApp uu____82518
                                   in
                                let uu____82532 =
                                  let tname_decl =
                                    let uu____82542 =
                                      let uu____82543 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____82562 =
                                                  let uu____82564 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____82564
                                                   in
                                                let uu____82566 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____82562, uu____82566,
                                                  false)))
                                         in
                                      let uu____82570 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____82543,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____82570, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____82542
                                     in
                                  let uu____82578 =
                                    match vars with
                                    | [] ->
                                        let uu____82591 =
                                          let uu____82592 =
                                            let uu____82595 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _82601  ->
                                                 FStar_Pervasives_Native.Some
                                                   _82601) uu____82595
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____82592
                                           in
                                        ([], uu____82591)
                                    | uu____82604 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____82614 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____82614
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____82630 =
                                            let uu____82638 =
                                              let uu____82639 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____82640 =
                                                let uu____82656 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____82656)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____82639 uu____82640
                                               in
                                            (uu____82638,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____82630
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____82578 with
                                  | (tok_decls,env2) ->
                                      let uu____82683 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____82683
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____82532 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____82711 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____82711 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____82733 =
                                                 let uu____82734 =
                                                   let uu____82742 =
                                                     let uu____82743 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____82743
                                                      in
                                                   (uu____82742,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____82734
                                                  in
                                               [uu____82733]
                                             else []  in
                                           let uu____82751 =
                                             let uu____82754 =
                                               let uu____82757 =
                                                 let uu____82760 =
                                                   let uu____82761 =
                                                     let uu____82769 =
                                                       let uu____82770 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____82771 =
                                                         let uu____82782 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____82782)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____82770
                                                         uu____82771
                                                        in
                                                     (uu____82769,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____82761
                                                    in
                                                 [uu____82760]  in
                                               FStar_List.append karr
                                                 uu____82757
                                                in
                                             FStar_All.pipe_right uu____82754
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____82751
                                        in
                                     let aux =
                                       let uu____82801 =
                                         let uu____82804 =
                                           inversion_axioms tapp vars  in
                                         let uu____82807 =
                                           let uu____82810 =
                                             let uu____82813 =
                                               let uu____82814 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____82814 env2
                                                 tapp vars
                                                in
                                             [uu____82813]  in
                                           FStar_All.pipe_right uu____82810
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____82804
                                           uu____82807
                                          in
                                       FStar_List.append kindingAx
                                         uu____82801
                                        in
                                     let g =
                                       let uu____82822 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____82822
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82830,uu____82831,uu____82832,uu____82833,uu____82834)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82842,t,uu____82844,n_tps,uu____82846) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____82856 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____82856 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82904 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82904 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____82928 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____82928 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____82948 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____82948 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83027 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83027,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83034 =
                                   let uu____83035 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83035, true)
                                    in
                                 let uu____83043 =
                                   let uu____83050 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83050
                                    in
                                 FStar_All.pipe_right uu____83034 uu____83043
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
                               let uu____83062 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____83062 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83074::uu____83075 ->
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
                                            let uu____83124 =
                                              let uu____83125 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83125]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83124
                                             in
                                          let uu____83151 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83152 =
                                            let uu____83163 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83163)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83151 uu____83152
                                      | uu____83190 -> tok_typing  in
                                    let uu____83201 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83201 with
                                     | (vars',guards',env'',decls_formals,uu____83226)
                                         ->
                                         let uu____83239 =
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
                                         (match uu____83239 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83269 ->
                                                    let uu____83278 =
                                                      let uu____83279 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83279
                                                       in
                                                    [uu____83278]
                                                 in
                                              let encode_elim uu____83295 =
                                                let uu____83296 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83296 with
                                                | (head1,args) ->
                                                    let uu____83347 =
                                                      let uu____83348 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83348.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83347 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83360;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83361;_},uu____83362)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83368 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83368
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
                                                                  | uu____83431
                                                                    ->
                                                                    let uu____83432
                                                                    =
                                                                    let uu____83438
                                                                    =
                                                                    let uu____83440
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83440
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83438)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83432
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83463
                                                                    =
                                                                    let uu____83465
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83465
                                                                     in
                                                                    if
                                                                    uu____83463
                                                                    then
                                                                    let uu____83487
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83487]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83490
                                                                =
                                                                let uu____83504
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83561
                                                                     ->
                                                                    fun
                                                                    uu____83562
                                                                     ->
                                                                    match 
                                                                    (uu____83561,
                                                                    uu____83562)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83673
                                                                    =
                                                                    let uu____83681
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83681
                                                                     in
                                                                    (match uu____83673
                                                                    with
                                                                    | 
                                                                    (uu____83695,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83706
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83706
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83711
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83711
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
                                                                  uu____83504
                                                                 in
                                                              (match uu____83490
                                                               with
                                                               | (uu____83732,arg_vars,elim_eqns_or_guards,uu____83735)
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
                                                                    let uu____83762
                                                                    =
                                                                    let uu____83770
                                                                    =
                                                                    let uu____83771
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83772
                                                                    =
                                                                    let uu____83783
                                                                    =
                                                                    let uu____83784
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83784
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83786
                                                                    =
                                                                    let uu____83787
                                                                    =
                                                                    let uu____83792
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83792)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83787
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83783,
                                                                    uu____83786)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83771
                                                                    uu____83772
                                                                     in
                                                                    (uu____83770,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83762
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83807
                                                                    =
                                                                    let uu____83808
                                                                    =
                                                                    let uu____83814
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83814,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83808
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83807
                                                                     in
                                                                    let uu____83817
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83817
                                                                    then
                                                                    let x =
                                                                    let uu____83821
                                                                    =
                                                                    let uu____83827
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83827,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83821
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83832
                                                                    =
                                                                    let uu____83840
                                                                    =
                                                                    let uu____83841
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83842
                                                                    =
                                                                    let uu____83853
                                                                    =
                                                                    let uu____83858
                                                                    =
                                                                    let uu____83861
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83861]
                                                                     in
                                                                    [uu____83858]
                                                                     in
                                                                    let uu____83866
                                                                    =
                                                                    let uu____83867
                                                                    =
                                                                    let uu____83872
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83872,
                                                                    uu____83874)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83867
                                                                     in
                                                                    (uu____83853,
                                                                    [x],
                                                                    uu____83866)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83841
                                                                    uu____83842
                                                                     in
                                                                    let uu____83895
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83840,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83895)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83832
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83906
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
                                                                    (let uu____83929
                                                                    =
                                                                    let uu____83930
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____83930
                                                                    dapp1  in
                                                                    [uu____83929])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83906
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____83937
                                                                    =
                                                                    let uu____83945
                                                                    =
                                                                    let uu____83946
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83947
                                                                    =
                                                                    let uu____83958
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83959
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83961
                                                                    =
                                                                    let uu____83962
                                                                    =
                                                                    let uu____83967
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____83967)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83962
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83958,
                                                                    uu____83961)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83946
                                                                    uu____83947
                                                                     in
                                                                    (uu____83945,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83937)
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
                                                         let uu____83986 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83986
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
                                                                  | uu____84049
                                                                    ->
                                                                    let uu____84050
                                                                    =
                                                                    let uu____84056
                                                                    =
                                                                    let uu____84058
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84058
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84056)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84050
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84081
                                                                    =
                                                                    let uu____84083
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84083
                                                                     in
                                                                    if
                                                                    uu____84081
                                                                    then
                                                                    let uu____84105
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84105]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84108
                                                                =
                                                                let uu____84122
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84179
                                                                     ->
                                                                    fun
                                                                    uu____84180
                                                                     ->
                                                                    match 
                                                                    (uu____84179,
                                                                    uu____84180)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84291
                                                                    =
                                                                    let uu____84299
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84299
                                                                     in
                                                                    (match uu____84291
                                                                    with
                                                                    | 
                                                                    (uu____84313,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84324
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84324
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84329
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84329
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
                                                                  uu____84122
                                                                 in
                                                              (match uu____84108
                                                               with
                                                               | (uu____84350,arg_vars,elim_eqns_or_guards,uu____84353)
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
                                                                    let uu____84380
                                                                    =
                                                                    let uu____84388
                                                                    =
                                                                    let uu____84389
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84390
                                                                    =
                                                                    let uu____84401
                                                                    =
                                                                    let uu____84402
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84402
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84404
                                                                    =
                                                                    let uu____84405
                                                                    =
                                                                    let uu____84410
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84410)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84405
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84401,
                                                                    uu____84404)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84389
                                                                    uu____84390
                                                                     in
                                                                    (uu____84388,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84380
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84425
                                                                    =
                                                                    let uu____84426
                                                                    =
                                                                    let uu____84432
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84432,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84426
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84425
                                                                     in
                                                                    let uu____84435
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84435
                                                                    then
                                                                    let x =
                                                                    let uu____84439
                                                                    =
                                                                    let uu____84445
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84445,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84439
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84450
                                                                    =
                                                                    let uu____84458
                                                                    =
                                                                    let uu____84459
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84460
                                                                    =
                                                                    let uu____84471
                                                                    =
                                                                    let uu____84476
                                                                    =
                                                                    let uu____84479
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84479]
                                                                     in
                                                                    [uu____84476]
                                                                     in
                                                                    let uu____84484
                                                                    =
                                                                    let uu____84485
                                                                    =
                                                                    let uu____84490
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84490,
                                                                    uu____84492)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84485
                                                                     in
                                                                    (uu____84471,
                                                                    [x],
                                                                    uu____84484)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84459
                                                                    uu____84460
                                                                     in
                                                                    let uu____84513
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84458,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84513)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84450
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84524
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
                                                                    (let uu____84547
                                                                    =
                                                                    let uu____84548
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84548
                                                                    dapp1  in
                                                                    [uu____84547])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84524
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84555
                                                                    =
                                                                    let uu____84563
                                                                    =
                                                                    let uu____84564
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84565
                                                                    =
                                                                    let uu____84576
                                                                    =
                                                                    let uu____84577
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84577
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84579
                                                                    =
                                                                    let uu____84580
                                                                    =
                                                                    let uu____84585
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84585)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84580
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84576,
                                                                    uu____84579)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84564
                                                                    uu____84565
                                                                     in
                                                                    (uu____84563,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84555)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84602 ->
                                                         ((let uu____84604 =
                                                             let uu____84610
                                                               =
                                                               let uu____84612
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84614
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84612
                                                                 uu____84614
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84610)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84604);
                                                          ([], [])))
                                                 in
                                              let uu____84622 =
                                                encode_elim ()  in
                                              (match uu____84622 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84648 =
                                                       let uu____84651 =
                                                         let uu____84654 =
                                                           let uu____84657 =
                                                             let uu____84660
                                                               =
                                                               let uu____84663
                                                                 =
                                                                 let uu____84666
                                                                   =
                                                                   let uu____84667
                                                                    =
                                                                    let uu____84679
                                                                    =
                                                                    let uu____84680
                                                                    =
                                                                    let uu____84682
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84682
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84680
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84679)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84667
                                                                    in
                                                                 [uu____84666]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84663
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84660
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84693 =
                                                             let uu____84696
                                                               =
                                                               let uu____84699
                                                                 =
                                                                 let uu____84702
                                                                   =
                                                                   let uu____84705
                                                                    =
                                                                    let uu____84708
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84713
                                                                    =
                                                                    let uu____84716
                                                                    =
                                                                    let uu____84717
                                                                    =
                                                                    let uu____84725
                                                                    =
                                                                    let uu____84726
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84727
                                                                    =
                                                                    let uu____84738
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84738)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84726
                                                                    uu____84727
                                                                     in
                                                                    (uu____84725,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84717
                                                                     in
                                                                    let uu____84751
                                                                    =
                                                                    let uu____84754
                                                                    =
                                                                    let uu____84755
                                                                    =
                                                                    let uu____84763
                                                                    =
                                                                    let uu____84764
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84765
                                                                    =
                                                                    let uu____84776
                                                                    =
                                                                    let uu____84777
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84777
                                                                    vars'  in
                                                                    let uu____84779
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84776,
                                                                    uu____84779)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84764
                                                                    uu____84765
                                                                     in
                                                                    (uu____84763,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84755
                                                                     in
                                                                    [uu____84754]
                                                                     in
                                                                    uu____84716
                                                                    ::
                                                                    uu____84751
                                                                     in
                                                                    uu____84708
                                                                    ::
                                                                    uu____84713
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84705
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84702
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84699
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84696
                                                              in
                                                           FStar_List.append
                                                             uu____84657
                                                             uu____84693
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84654
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84651
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84648
                                                      in
                                                   let uu____84796 =
                                                     let uu____84797 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84797 g
                                                      in
                                                   (uu____84796, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84831  ->
              fun se  ->
                match uu____84831 with
                | (g,env1) ->
                    let uu____84851 = encode_sigelt env1 se  in
                    (match uu____84851 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____84919 =
        match uu____84919 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____84956 ->
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
                 ((let uu____84964 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____84964
                   then
                     let uu____84969 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____84971 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____84973 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____84969 uu____84971 uu____84973
                   else ());
                  (let uu____84978 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____84978 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____84996 =
                         let uu____85004 =
                           let uu____85006 =
                             let uu____85008 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85008
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85006  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85004
                          in
                       (match uu____84996 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85028 = FStar_Options.log_queries ()
                                 in
                              if uu____85028
                              then
                                let uu____85031 =
                                  let uu____85033 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85035 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85037 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85033 uu____85035 uu____85037
                                   in
                                FStar_Pervasives_Native.Some uu____85031
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85053 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85063 =
                                let uu____85066 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85066  in
                              FStar_List.append uu____85053 uu____85063  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85078,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85098 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85098 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85119 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85119 with | (uu____85146,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85199  ->
              match uu____85199 with
              | (l,uu____85208,uu____85209) ->
                  let uu____85212 =
                    let uu____85224 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85224, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85212))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85257  ->
              match uu____85257 with
              | (l,uu____85268,uu____85269) ->
                  let uu____85272 =
                    let uu____85273 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85276  -> FStar_SMTEncoding_Term.Echo _85276)
                      uu____85273
                     in
                  let uu____85277 =
                    let uu____85280 =
                      let uu____85281 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85281  in
                    [uu____85280]  in
                  uu____85272 :: uu____85277))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85299 =
      let uu____85302 =
        let uu____85303 = FStar_Util.psmap_empty ()  in
        let uu____85318 =
          let uu____85327 = FStar_Util.psmap_empty ()  in (uu____85327, [])
           in
        let uu____85334 =
          let uu____85336 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85336 FStar_Ident.string_of_lid  in
        let uu____85338 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85303;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85318;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85334;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85338
        }  in
      [uu____85302]  in
    FStar_ST.op_Colon_Equals last_env uu____85299
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85382 = FStar_ST.op_Bang last_env  in
      match uu____85382 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85410 ->
          let uu___2175_85413 = e  in
          let uu____85414 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_85413.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_85413.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_85413.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_85413.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_85413.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_85413.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_85413.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85414;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_85413.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_85413.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85422 = FStar_ST.op_Bang last_env  in
    match uu____85422 with
    | [] -> failwith "Empty env stack"
    | uu____85449::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85481  ->
    let uu____85482 = FStar_ST.op_Bang last_env  in
    match uu____85482 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85542  ->
    let uu____85543 = FStar_ST.op_Bang last_env  in
    match uu____85543 with
    | [] -> failwith "Popping an empty stack"
    | uu____85570::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85607  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85660  ->
         let uu____85661 = snapshot_env ()  in
         match uu____85661 with
         | (env_depth,()) ->
             let uu____85683 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85683 with
              | (varops_depth,()) ->
                  let uu____85705 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85705 with
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
        (fun uu____85763  ->
           let uu____85764 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85764 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85859 = snapshot msg  in () 
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
        | (uu____85905::uu____85906,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_85914 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_85914.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_85914.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_85914.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____85915 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_85942 = elt  in
        let uu____85943 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_85942.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_85942.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____85943;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_85942.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____85963 =
        let uu____85966 =
          let uu____85967 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____85967  in
        let uu____85968 = open_fact_db_tags env  in uu____85966 ::
          uu____85968
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____85963
  
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
      let uu____85995 = encode_sigelt env se  in
      match uu____85995 with
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
                (let uu____86041 =
                   let uu____86044 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86044
                    in
                 match uu____86041 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86059 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86059
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86089 = FStar_Options.log_queries ()  in
        if uu____86089
        then
          let uu____86094 =
            let uu____86095 =
              let uu____86097 =
                let uu____86099 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86099 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86097  in
            FStar_SMTEncoding_Term.Caption uu____86095  in
          uu____86094 :: decls
        else decls  in
      (let uu____86118 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86118
       then
         let uu____86121 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86121
       else ());
      (let env =
         let uu____86127 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86127 tcenv  in
       let uu____86128 = encode_top_level_facts env se  in
       match uu____86128 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86142 =
               let uu____86145 =
                 let uu____86148 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86148
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86145  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86142)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86181 = FStar_Options.log_queries ()  in
          if uu____86181
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_86201 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_86201.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_86201.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_86201.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_86201.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_86201.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_86201.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_86201.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_86201.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_86201.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_86201.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86206 =
             let uu____86209 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86209
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86206  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86229 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86229
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
          (let uu____86253 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86253
           then
             let uu____86256 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86256
           else ());
          (let env =
             let uu____86264 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86264
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86303  ->
                     fun se  ->
                       match uu____86303 with
                       | (g,env2) ->
                           let uu____86323 = encode_top_level_facts env2 se
                              in
                           (match uu____86323 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86346 =
             encode_signature
               (let uu___2303_86355 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_86355.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_86355.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_86355.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_86355.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_86355.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_86355.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_86355.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_86355.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_86355.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_86355.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86346 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86371 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86371
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86377 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86377))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86405  ->
        match uu____86405 with
        | (decls,fvbs) ->
            ((let uu____86419 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86419
              then ()
              else
                (let uu____86424 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86424
                 then
                   let uu____86427 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86427
                 else ()));
             (let env =
                let uu____86435 = get_env name tcenv  in
                FStar_All.pipe_right uu____86435
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86437 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86437
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86451 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86451
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
        (let uu____86513 =
           let uu____86515 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86515.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86513);
        (let env =
           let uu____86517 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86517 tcenv  in
         let uu____86518 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86557 = aux rest  in
                 (match uu____86557 with
                  | (out,rest1) ->
                      let t =
                        let uu____86585 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86585 with
                        | FStar_Pervasives_Native.Some uu____86588 ->
                            let uu____86589 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86589
                              x.FStar_Syntax_Syntax.sort
                        | uu____86590 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86594 =
                        let uu____86597 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_86600 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_86600.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_86600.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86597 :: out  in
                      (uu____86594, rest1))
             | uu____86605 -> ([], bindings)  in
           let uu____86612 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86612 with
           | (closing,bindings) ->
               let uu____86639 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86639, bindings)
            in
         match uu____86518 with
         | (q1,bindings) ->
             let uu____86670 = encode_env_bindings env bindings  in
             (match uu____86670 with
              | (env_decls,env1) ->
                  ((let uu____86692 =
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
                    if uu____86692
                    then
                      let uu____86699 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86699
                    else ());
                   (let uu____86704 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86704 with
                    | (phi,qdecls) ->
                        let uu____86725 =
                          let uu____86730 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86730 phi
                           in
                        (match uu____86725 with
                         | (labels,phi1) ->
                             let uu____86747 = encode_labels labels  in
                             (match uu____86747 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86783 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86783
                                    then
                                      let uu____86788 =
                                        let uu____86789 =
                                          let uu____86791 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86791
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86789
                                         in
                                      [uu____86788]
                                    else []  in
                                  let query_prelude =
                                    let uu____86799 =
                                      let uu____86800 =
                                        let uu____86801 =
                                          let uu____86804 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86811 =
                                            let uu____86814 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86814
                                             in
                                          FStar_List.append uu____86804
                                            uu____86811
                                           in
                                        FStar_List.append env_decls
                                          uu____86801
                                         in
                                      FStar_All.pipe_right uu____86800
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86799
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86824 =
                                      let uu____86832 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86833 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86832,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86833)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86824
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
  