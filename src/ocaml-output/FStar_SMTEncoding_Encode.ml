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
  let uu____72876 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72876 with
  | (asym,a) ->
      let uu____72887 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72887 with
       | (xsym,x) ->
           let uu____72898 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72898 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72976 =
                      let uu____72988 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72988, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72976  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____73008 =
                      let uu____73016 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____73016)  in
                    FStar_SMTEncoding_Util.mkApp uu____73008  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____73035 =
                    let uu____73038 =
                      let uu____73041 =
                        let uu____73044 =
                          let uu____73045 =
                            let uu____73053 =
                              let uu____73054 =
                                let uu____73065 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____73065)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____73054
                               in
                            (uu____73053, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____73045  in
                        let uu____73077 =
                          let uu____73080 =
                            let uu____73081 =
                              let uu____73089 =
                                let uu____73090 =
                                  let uu____73101 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____73101)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____73090
                                 in
                              (uu____73089,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____73081  in
                          [uu____73080]  in
                        uu____73044 :: uu____73077  in
                      xtok_decl :: uu____73041  in
                    xname_decl :: uu____73038  in
                  (xtok1, (FStar_List.length vars), uu____73035)  in
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
                  let uu____73271 =
                    let uu____73292 =
                      let uu____73311 =
                        let uu____73312 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73312
                         in
                      quant axy uu____73311  in
                    (FStar_Parser_Const.op_Eq, uu____73292)  in
                  let uu____73329 =
                    let uu____73352 =
                      let uu____73373 =
                        let uu____73392 =
                          let uu____73393 =
                            let uu____73394 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73394  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73393
                           in
                        quant axy uu____73392  in
                      (FStar_Parser_Const.op_notEq, uu____73373)  in
                    let uu____73411 =
                      let uu____73434 =
                        let uu____73455 =
                          let uu____73474 =
                            let uu____73475 =
                              let uu____73476 =
                                let uu____73481 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73482 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73481, uu____73482)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73476  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73475
                             in
                          quant xy uu____73474  in
                        (FStar_Parser_Const.op_And, uu____73455)  in
                      let uu____73499 =
                        let uu____73522 =
                          let uu____73543 =
                            let uu____73562 =
                              let uu____73563 =
                                let uu____73564 =
                                  let uu____73569 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73570 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73569, uu____73570)  in
                                FStar_SMTEncoding_Util.mkOr uu____73564  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73563
                               in
                            quant xy uu____73562  in
                          (FStar_Parser_Const.op_Or, uu____73543)  in
                        let uu____73587 =
                          let uu____73610 =
                            let uu____73631 =
                              let uu____73650 =
                                let uu____73651 =
                                  let uu____73652 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73652
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73651
                                 in
                              quant qx uu____73650  in
                            (FStar_Parser_Const.op_Negation, uu____73631)  in
                          let uu____73669 =
                            let uu____73692 =
                              let uu____73713 =
                                let uu____73732 =
                                  let uu____73733 =
                                    let uu____73734 =
                                      let uu____73739 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73740 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73739, uu____73740)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73734
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73733
                                   in
                                quant xy uu____73732  in
                              (FStar_Parser_Const.op_LT, uu____73713)  in
                            let uu____73757 =
                              let uu____73780 =
                                let uu____73801 =
                                  let uu____73820 =
                                    let uu____73821 =
                                      let uu____73822 =
                                        let uu____73827 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73828 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73827, uu____73828)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73822
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73821
                                     in
                                  quant xy uu____73820  in
                                (FStar_Parser_Const.op_LTE, uu____73801)  in
                              let uu____73845 =
                                let uu____73868 =
                                  let uu____73889 =
                                    let uu____73908 =
                                      let uu____73909 =
                                        let uu____73910 =
                                          let uu____73915 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73916 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73915, uu____73916)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73910
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73909
                                       in
                                    quant xy uu____73908  in
                                  (FStar_Parser_Const.op_GT, uu____73889)  in
                                let uu____73933 =
                                  let uu____73956 =
                                    let uu____73977 =
                                      let uu____73996 =
                                        let uu____73997 =
                                          let uu____73998 =
                                            let uu____74003 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____74004 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____74003, uu____74004)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73998
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73997
                                         in
                                      quant xy uu____73996  in
                                    (FStar_Parser_Const.op_GTE, uu____73977)
                                     in
                                  let uu____74021 =
                                    let uu____74044 =
                                      let uu____74065 =
                                        let uu____74084 =
                                          let uu____74085 =
                                            let uu____74086 =
                                              let uu____74091 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____74092 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____74091, uu____74092)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____74086
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____74085
                                           in
                                        quant xy uu____74084  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____74065)
                                       in
                                    let uu____74109 =
                                      let uu____74132 =
                                        let uu____74153 =
                                          let uu____74172 =
                                            let uu____74173 =
                                              let uu____74174 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74174
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74173
                                             in
                                          quant qx uu____74172  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74153)
                                         in
                                      let uu____74191 =
                                        let uu____74214 =
                                          let uu____74235 =
                                            let uu____74254 =
                                              let uu____74255 =
                                                let uu____74256 =
                                                  let uu____74261 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74262 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74261, uu____74262)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74256
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74255
                                               in
                                            quant xy uu____74254  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74235)
                                           in
                                        let uu____74279 =
                                          let uu____74302 =
                                            let uu____74323 =
                                              let uu____74342 =
                                                let uu____74343 =
                                                  let uu____74344 =
                                                    let uu____74349 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74350 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74349,
                                                      uu____74350)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74344
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74343
                                                 in
                                              quant xy uu____74342  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74323)
                                             in
                                          let uu____74367 =
                                            let uu____74390 =
                                              let uu____74411 =
                                                let uu____74430 =
                                                  let uu____74431 =
                                                    let uu____74432 =
                                                      let uu____74437 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74438 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74437,
                                                        uu____74438)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74432
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74431
                                                   in
                                                quant xy uu____74430  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74411)
                                               in
                                            let uu____74455 =
                                              let uu____74478 =
                                                let uu____74499 =
                                                  let uu____74518 =
                                                    let uu____74519 =
                                                      let uu____74520 =
                                                        let uu____74525 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74526 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74525,
                                                          uu____74526)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74520
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74519
                                                     in
                                                  quant xy uu____74518  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74499)
                                                 in
                                              let uu____74543 =
                                                let uu____74566 =
                                                  let uu____74587 =
                                                    let uu____74606 =
                                                      let uu____74607 =
                                                        let uu____74608 =
                                                          let uu____74613 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74614 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74613,
                                                            uu____74614)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74608
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74607
                                                       in
                                                    quant xy uu____74606  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74587)
                                                   in
                                                let uu____74631 =
                                                  let uu____74654 =
                                                    let uu____74675 =
                                                      let uu____74694 =
                                                        let uu____74695 =
                                                          let uu____74696 =
                                                            let uu____74701 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74702 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74701,
                                                              uu____74702)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74696
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74695
                                                         in
                                                      quant xy uu____74694
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74675)
                                                     in
                                                  let uu____74719 =
                                                    let uu____74742 =
                                                      let uu____74763 =
                                                        let uu____74782 =
                                                          let uu____74783 =
                                                            let uu____74784 =
                                                              let uu____74789
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74790
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74789,
                                                                uu____74790)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74784
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74783
                                                           in
                                                        quant xy uu____74782
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74763)
                                                       in
                                                    let uu____74807 =
                                                      let uu____74830 =
                                                        let uu____74851 =
                                                          let uu____74870 =
                                                            let uu____74871 =
                                                              let uu____74872
                                                                =
                                                                let uu____74877
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74878
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74877,
                                                                  uu____74878)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74872
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74871
                                                             in
                                                          quant xy
                                                            uu____74870
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74851)
                                                         in
                                                      let uu____74895 =
                                                        let uu____74918 =
                                                          let uu____74939 =
                                                            let uu____74958 =
                                                              let uu____74959
                                                                =
                                                                let uu____74960
                                                                  =
                                                                  let uu____74965
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74966
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74965,
                                                                    uu____74966)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74960
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74959
                                                               in
                                                            quant xy
                                                              uu____74958
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74939)
                                                           in
                                                        let uu____74983 =
                                                          let uu____75006 =
                                                            let uu____75027 =
                                                              let uu____75046
                                                                =
                                                                let uu____75047
                                                                  =
                                                                  let uu____75048
                                                                    =
                                                                    let uu____75053
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75054
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75053,
                                                                    uu____75054)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____75048
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____75047
                                                                 in
                                                              quant xy
                                                                uu____75046
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____75027)
                                                             in
                                                          let uu____75071 =
                                                            let uu____75094 =
                                                              let uu____75115
                                                                =
                                                                let uu____75134
                                                                  =
                                                                  let uu____75135
                                                                    =
                                                                    let uu____75136
                                                                    =
                                                                    let uu____75141
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75142
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75141,
                                                                    uu____75142)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75136
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75135
                                                                   in
                                                                quant xy
                                                                  uu____75134
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75115)
                                                               in
                                                            let uu____75159 =
                                                              let uu____75182
                                                                =
                                                                let uu____75203
                                                                  =
                                                                  let uu____75222
                                                                    =
                                                                    let uu____75223
                                                                    =
                                                                    let uu____75224
                                                                    =
                                                                    let uu____75229
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75230
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75229,
                                                                    uu____75230)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75224
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75223
                                                                     in
                                                                  quant xy
                                                                    uu____75222
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75203)
                                                                 in
                                                              let uu____75247
                                                                =
                                                                let uu____75270
                                                                  =
                                                                  let uu____75291
                                                                    =
                                                                    let uu____75310
                                                                    =
                                                                    let uu____75311
                                                                    =
                                                                    let uu____75312
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75312
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75311
                                                                     in
                                                                    quant qx
                                                                    uu____75310
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75291)
                                                                   in
                                                                [uu____75270]
                                                                 in
                                                              uu____75182 ::
                                                                uu____75247
                                                               in
                                                            uu____75094 ::
                                                              uu____75159
                                                             in
                                                          uu____75006 ::
                                                            uu____75071
                                                           in
                                                        uu____74918 ::
                                                          uu____74983
                                                         in
                                                      uu____74830 ::
                                                        uu____74895
                                                       in
                                                    uu____74742 ::
                                                      uu____74807
                                                     in
                                                  uu____74654 :: uu____74719
                                                   in
                                                uu____74566 :: uu____74631
                                                 in
                                              uu____74478 :: uu____74543  in
                                            uu____74390 :: uu____74455  in
                                          uu____74302 :: uu____74367  in
                                        uu____74214 :: uu____74279  in
                                      uu____74132 :: uu____74191  in
                                    uu____74044 :: uu____74109  in
                                  uu____73956 :: uu____74021  in
                                uu____73868 :: uu____73933  in
                              uu____73780 :: uu____73845  in
                            uu____73692 :: uu____73757  in
                          uu____73610 :: uu____73669  in
                        uu____73522 :: uu____73587  in
                      uu____73434 :: uu____73499  in
                    uu____73352 :: uu____73411  in
                  uu____73271 :: uu____73329  in
                let mk1 l v1 =
                  let uu____75851 =
                    let uu____75863 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75953  ->
                              match uu____75953 with
                              | (l',uu____75974) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75863
                      (FStar_Option.map
                         (fun uu____76073  ->
                            match uu____76073 with
                            | (uu____76101,b) ->
                                let uu____76135 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76135 v1))
                     in
                  FStar_All.pipe_right uu____75851 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76218  ->
                          match uu____76218 with
                          | (l',uu____76239) -> FStar_Ident.lid_equals l l'))
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
          let uu____76313 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76313 with
          | (xxsym,xx) ->
              let uu____76324 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76324 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76340 =
                     let uu____76348 =
                       let uu____76349 =
                         let uu____76360 =
                           let uu____76361 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76371 =
                             let uu____76382 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76382 :: vars  in
                           uu____76361 :: uu____76371  in
                         let uu____76408 =
                           let uu____76409 =
                             let uu____76414 =
                               let uu____76415 =
                                 let uu____76420 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76420)  in
                               FStar_SMTEncoding_Util.mkEq uu____76415  in
                             (xx_has_type, uu____76414)  in
                           FStar_SMTEncoding_Util.mkImp uu____76409  in
                         ([[xx_has_type]], uu____76360, uu____76408)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76349  in
                     let uu____76433 =
                       let uu____76435 =
                         let uu____76437 =
                           let uu____76439 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76439  in
                         Prims.op_Hat module_name uu____76437  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76435
                        in
                     (uu____76348,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76433)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76340)
  
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
    let uu____76495 =
      let uu____76497 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76497  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76495  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76519 =
      let uu____76520 =
        let uu____76528 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76528, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76520  in
    let uu____76533 =
      let uu____76536 =
        let uu____76537 =
          let uu____76545 =
            let uu____76546 =
              let uu____76557 =
                let uu____76558 =
                  let uu____76563 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76563)  in
                FStar_SMTEncoding_Util.mkImp uu____76558  in
              ([[typing_pred]], [xx], uu____76557)  in
            let uu____76588 =
              let uu____76603 = FStar_TypeChecker_Env.get_range env  in
              let uu____76604 = mkForall_fuel1 env  in
              uu____76604 uu____76603  in
            uu____76588 uu____76546  in
          (uu____76545, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76537  in
      [uu____76536]  in
    uu____76519 :: uu____76533  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76651 =
      let uu____76652 =
        let uu____76660 =
          let uu____76661 = FStar_TypeChecker_Env.get_range env  in
          let uu____76662 =
            let uu____76673 =
              let uu____76678 =
                let uu____76681 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76681]  in
              [uu____76678]  in
            let uu____76686 =
              let uu____76687 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76687 tt  in
            (uu____76673, [bb], uu____76686)  in
          FStar_SMTEncoding_Term.mkForall uu____76661 uu____76662  in
        (uu____76660, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76652  in
    let uu____76712 =
      let uu____76715 =
        let uu____76716 =
          let uu____76724 =
            let uu____76725 =
              let uu____76736 =
                let uu____76737 =
                  let uu____76742 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76742)  in
                FStar_SMTEncoding_Util.mkImp uu____76737  in
              ([[typing_pred]], [xx], uu____76736)  in
            let uu____76769 =
              let uu____76784 = FStar_TypeChecker_Env.get_range env  in
              let uu____76785 = mkForall_fuel1 env  in
              uu____76785 uu____76784  in
            uu____76769 uu____76725  in
          (uu____76724, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76716  in
      [uu____76715]  in
    uu____76651 :: uu____76712  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76828 =
        let uu____76829 =
          let uu____76835 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76835, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76829  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76828  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76849 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76849  in
    let uu____76854 =
      let uu____76855 =
        let uu____76863 =
          let uu____76864 = FStar_TypeChecker_Env.get_range env  in
          let uu____76865 =
            let uu____76876 =
              let uu____76881 =
                let uu____76884 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76884]  in
              [uu____76881]  in
            let uu____76889 =
              let uu____76890 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76890 tt  in
            (uu____76876, [bb], uu____76889)  in
          FStar_SMTEncoding_Term.mkForall uu____76864 uu____76865  in
        (uu____76863, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76855  in
    let uu____76915 =
      let uu____76918 =
        let uu____76919 =
          let uu____76927 =
            let uu____76928 =
              let uu____76939 =
                let uu____76940 =
                  let uu____76945 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76945)  in
                FStar_SMTEncoding_Util.mkImp uu____76940  in
              ([[typing_pred]], [xx], uu____76939)  in
            let uu____76972 =
              let uu____76987 = FStar_TypeChecker_Env.get_range env  in
              let uu____76988 = mkForall_fuel1 env  in
              uu____76988 uu____76987  in
            uu____76972 uu____76928  in
          (uu____76927, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76919  in
      let uu____77010 =
        let uu____77013 =
          let uu____77014 =
            let uu____77022 =
              let uu____77023 =
                let uu____77034 =
                  let uu____77035 =
                    let uu____77040 =
                      let uu____77041 =
                        let uu____77044 =
                          let uu____77047 =
                            let uu____77050 =
                              let uu____77051 =
                                let uu____77056 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____77057 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____77056, uu____77057)  in
                              FStar_SMTEncoding_Util.mkGT uu____77051  in
                            let uu____77059 =
                              let uu____77062 =
                                let uu____77063 =
                                  let uu____77068 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____77069 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____77068, uu____77069)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77063  in
                              let uu____77071 =
                                let uu____77074 =
                                  let uu____77075 =
                                    let uu____77080 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____77081 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____77080, uu____77081)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77075  in
                                [uu____77074]  in
                              uu____77062 :: uu____77071  in
                            uu____77050 :: uu____77059  in
                          typing_pred_y :: uu____77047  in
                        typing_pred :: uu____77044  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77041  in
                    (uu____77040, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77035  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77034)
                 in
              let uu____77114 =
                let uu____77129 = FStar_TypeChecker_Env.get_range env  in
                let uu____77130 = mkForall_fuel1 env  in
                uu____77130 uu____77129  in
              uu____77114 uu____77023  in
            (uu____77022,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77014  in
        [uu____77013]  in
      uu____76918 :: uu____77010  in
    uu____76854 :: uu____76915  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77173 =
        let uu____77174 =
          let uu____77180 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77180, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77174  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77173  in
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
      let uu____77196 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77196  in
    let uu____77201 =
      let uu____77202 =
        let uu____77210 =
          let uu____77211 = FStar_TypeChecker_Env.get_range env  in
          let uu____77212 =
            let uu____77223 =
              let uu____77228 =
                let uu____77231 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77231]  in
              [uu____77228]  in
            let uu____77236 =
              let uu____77237 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77237 tt  in
            (uu____77223, [bb], uu____77236)  in
          FStar_SMTEncoding_Term.mkForall uu____77211 uu____77212  in
        (uu____77210, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77202  in
    let uu____77262 =
      let uu____77265 =
        let uu____77266 =
          let uu____77274 =
            let uu____77275 =
              let uu____77286 =
                let uu____77287 =
                  let uu____77292 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77292)  in
                FStar_SMTEncoding_Util.mkImp uu____77287  in
              ([[typing_pred]], [xx], uu____77286)  in
            let uu____77319 =
              let uu____77334 = FStar_TypeChecker_Env.get_range env  in
              let uu____77335 = mkForall_fuel1 env  in
              uu____77335 uu____77334  in
            uu____77319 uu____77275  in
          (uu____77274, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77266  in
      let uu____77357 =
        let uu____77360 =
          let uu____77361 =
            let uu____77369 =
              let uu____77370 =
                let uu____77381 =
                  let uu____77382 =
                    let uu____77387 =
                      let uu____77388 =
                        let uu____77391 =
                          let uu____77394 =
                            let uu____77397 =
                              let uu____77398 =
                                let uu____77403 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77404 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77403, uu____77404)  in
                              FStar_SMTEncoding_Util.mkGT uu____77398  in
                            let uu____77406 =
                              let uu____77409 =
                                let uu____77410 =
                                  let uu____77415 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77416 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77415, uu____77416)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77410  in
                              let uu____77418 =
                                let uu____77421 =
                                  let uu____77422 =
                                    let uu____77427 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77428 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77427, uu____77428)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77422  in
                                [uu____77421]  in
                              uu____77409 :: uu____77418  in
                            uu____77397 :: uu____77406  in
                          typing_pred_y :: uu____77394  in
                        typing_pred :: uu____77391  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77388  in
                    (uu____77387, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77382  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77381)
                 in
              let uu____77461 =
                let uu____77476 = FStar_TypeChecker_Env.get_range env  in
                let uu____77477 = mkForall_fuel1 env  in
                uu____77477 uu____77476  in
              uu____77461 uu____77370  in
            (uu____77369,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77361  in
        [uu____77360]  in
      uu____77265 :: uu____77357  in
    uu____77201 :: uu____77262  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77524 =
      let uu____77525 =
        let uu____77533 =
          let uu____77534 = FStar_TypeChecker_Env.get_range env  in
          let uu____77535 =
            let uu____77546 =
              let uu____77551 =
                let uu____77554 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77554]  in
              [uu____77551]  in
            let uu____77559 =
              let uu____77560 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77560 tt  in
            (uu____77546, [bb], uu____77559)  in
          FStar_SMTEncoding_Term.mkForall uu____77534 uu____77535  in
        (uu____77533, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77525  in
    let uu____77585 =
      let uu____77588 =
        let uu____77589 =
          let uu____77597 =
            let uu____77598 =
              let uu____77609 =
                let uu____77610 =
                  let uu____77615 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77615)  in
                FStar_SMTEncoding_Util.mkImp uu____77610  in
              ([[typing_pred]], [xx], uu____77609)  in
            let uu____77642 =
              let uu____77657 = FStar_TypeChecker_Env.get_range env  in
              let uu____77658 = mkForall_fuel1 env  in
              uu____77658 uu____77657  in
            uu____77642 uu____77598  in
          (uu____77597, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77589  in
      [uu____77588]  in
    uu____77524 :: uu____77585  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77705 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77705]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77735 =
      let uu____77736 =
        let uu____77744 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77744, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77736  in
    [uu____77735]  in
  let mk_and_interp env conj uu____77767 =
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
    let uu____77796 =
      let uu____77797 =
        let uu____77805 =
          let uu____77806 = FStar_TypeChecker_Env.get_range env  in
          let uu____77807 =
            let uu____77818 =
              let uu____77819 =
                let uu____77824 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77824, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77819  in
            ([[l_and_a_b]], [aa; bb], uu____77818)  in
          FStar_SMTEncoding_Term.mkForall uu____77806 uu____77807  in
        (uu____77805, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77797  in
    [uu____77796]  in
  let mk_or_interp env disj uu____77879 =
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
    let uu____77908 =
      let uu____77909 =
        let uu____77917 =
          let uu____77918 = FStar_TypeChecker_Env.get_range env  in
          let uu____77919 =
            let uu____77930 =
              let uu____77931 =
                let uu____77936 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77936, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77931  in
            ([[l_or_a_b]], [aa; bb], uu____77930)  in
          FStar_SMTEncoding_Term.mkForall uu____77918 uu____77919  in
        (uu____77917, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77909  in
    [uu____77908]  in
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
    let uu____78014 =
      let uu____78015 =
        let uu____78023 =
          let uu____78024 = FStar_TypeChecker_Env.get_range env  in
          let uu____78025 =
            let uu____78036 =
              let uu____78037 =
                let uu____78042 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78042, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78037  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____78036)  in
          FStar_SMTEncoding_Term.mkForall uu____78024 uu____78025  in
        (uu____78023, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78015  in
    [uu____78014]  in
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
    let uu____78132 =
      let uu____78133 =
        let uu____78141 =
          let uu____78142 = FStar_TypeChecker_Env.get_range env  in
          let uu____78143 =
            let uu____78154 =
              let uu____78155 =
                let uu____78160 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78160, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78155  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78154)  in
          FStar_SMTEncoding_Term.mkForall uu____78142 uu____78143  in
        (uu____78141, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78133  in
    [uu____78132]  in
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
    let uu____78260 =
      let uu____78261 =
        let uu____78269 =
          let uu____78270 = FStar_TypeChecker_Env.get_range env  in
          let uu____78271 =
            let uu____78282 =
              let uu____78283 =
                let uu____78288 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78288, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78283  in
            ([[l_imp_a_b]], [aa; bb], uu____78282)  in
          FStar_SMTEncoding_Term.mkForall uu____78270 uu____78271  in
        (uu____78269, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78261  in
    [uu____78260]  in
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
    let uu____78372 =
      let uu____78373 =
        let uu____78381 =
          let uu____78382 = FStar_TypeChecker_Env.get_range env  in
          let uu____78383 =
            let uu____78394 =
              let uu____78395 =
                let uu____78400 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78400, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78395  in
            ([[l_iff_a_b]], [aa; bb], uu____78394)  in
          FStar_SMTEncoding_Term.mkForall uu____78382 uu____78383  in
        (uu____78381, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78373  in
    [uu____78372]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78471 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78471  in
    let uu____78476 =
      let uu____78477 =
        let uu____78485 =
          let uu____78486 = FStar_TypeChecker_Env.get_range env  in
          let uu____78487 =
            let uu____78498 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78498)  in
          FStar_SMTEncoding_Term.mkForall uu____78486 uu____78487  in
        (uu____78485, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78477  in
    [uu____78476]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78551 =
      let uu____78552 =
        let uu____78560 =
          let uu____78561 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78561 range_ty  in
        let uu____78562 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78560, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78562)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78552  in
    [uu____78551]  in
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
        let uu____78608 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78608 x1 t  in
      let uu____78610 = FStar_TypeChecker_Env.get_range env  in
      let uu____78611 =
        let uu____78622 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78622)  in
      FStar_SMTEncoding_Term.mkForall uu____78610 uu____78611  in
    let uu____78647 =
      let uu____78648 =
        let uu____78656 =
          let uu____78657 = FStar_TypeChecker_Env.get_range env  in
          let uu____78658 =
            let uu____78669 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78669)  in
          FStar_SMTEncoding_Term.mkForall uu____78657 uu____78658  in
        (uu____78656,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78648  in
    [uu____78647]  in
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
    let uu____78730 =
      let uu____78731 =
        let uu____78739 =
          let uu____78740 = FStar_TypeChecker_Env.get_range env  in
          let uu____78741 =
            let uu____78757 =
              let uu____78758 =
                let uu____78763 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78764 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78763, uu____78764)  in
              FStar_SMTEncoding_Util.mkAnd uu____78758  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78757)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78740 uu____78741  in
        (uu____78739,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78731  in
    [uu____78730]  in
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
          let uu____79322 =
            FStar_Util.find_opt
              (fun uu____79360  ->
                 match uu____79360 with
                 | (l,uu____79376) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79322 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79419,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79480 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79480 with
        | (form,decls) ->
            let uu____79489 =
              let uu____79492 =
                let uu____79495 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79495]  in
              FStar_All.pipe_right uu____79492
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79489
  
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
              let uu____79554 =
                ((let uu____79558 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79558) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79554
              then
                let arg_sorts =
                  let uu____79570 =
                    let uu____79571 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79571.FStar_Syntax_Syntax.n  in
                  match uu____79570 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79577) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79615  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79622 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79624 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79624 with
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
                    let uu____79660 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79660, env1)
              else
                (let uu____79665 = prims.is lid  in
                 if uu____79665
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79674 = prims.mk lid vname  in
                   match uu____79674 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79698 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79698, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79707 =
                      let uu____79726 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79726 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79754 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79754
                            then
                              let uu____79759 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79762 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79762.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79762.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79762.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79762.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79762.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79762.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79762.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79762.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79762.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79762.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79762.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79762.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79762.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79762.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79762.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79762.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79762.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79762.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79762.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79762.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79762.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79762.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79762.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79762.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79762.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79762.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79762.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79762.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79762.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79762.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79762.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79762.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79762.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79762.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79762.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79762.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79762.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79762.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79762.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79762.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79762.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79762.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79759
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79785 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79785)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79707 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79891  ->
                                  match uu___639_79891 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79895 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79895 with
                                       | (uu____79928,xxv) ->
                                           let xx =
                                             let uu____79967 =
                                               let uu____79968 =
                                                 let uu____79974 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79974,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79968
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79967
                                              in
                                           let uu____79977 =
                                             let uu____79978 =
                                               let uu____79986 =
                                                 let uu____79987 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79988 =
                                                   let uu____79999 =
                                                     let uu____80000 =
                                                       let uu____80005 =
                                                         let uu____80006 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____80006
                                                          in
                                                       (vapp, uu____80005)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____80000
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79999)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79987 uu____79988
                                                  in
                                               (uu____79986,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79978
                                              in
                                           [uu____79977])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____80021 =
                                        FStar_Util.prefix vars  in
                                      (match uu____80021 with
                                       | (uu____80054,xxv) ->
                                           let xx =
                                             let uu____80093 =
                                               let uu____80094 =
                                                 let uu____80100 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____80100,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____80094
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____80093
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
                                           let uu____80111 =
                                             let uu____80112 =
                                               let uu____80120 =
                                                 let uu____80121 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80122 =
                                                   let uu____80133 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80133)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80121 uu____80122
                                                  in
                                               (uu____80120,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80112
                                              in
                                           [uu____80111])
                                  | uu____80146 -> []))
                           in
                        let uu____80147 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80147 with
                         | (vars,guards,env',decls1,uu____80172) ->
                             let uu____80185 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80198 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80198, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80202 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80202 with
                                    | (g,ds) ->
                                        let uu____80215 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80215,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80185 with
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
                                  let should_thunk uu____80238 =
                                    let is_type1 t =
                                      let uu____80246 =
                                        let uu____80247 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80247.FStar_Syntax_Syntax.n  in
                                      match uu____80246 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80251 -> true
                                      | uu____80253 -> false  in
                                    let is_squash1 t =
                                      let uu____80262 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80262 with
                                      | (head1,uu____80281) ->
                                          let uu____80306 =
                                            let uu____80307 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80307.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80306 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80312;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80313;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80315;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80316;_};_},uu____80317)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80325 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80330 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80330))
                                       &&
                                       (let uu____80336 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80336))
                                      &&
                                      (let uu____80339 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80339)
                                     in
                                  let uu____80341 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80400 -> (false, vars)  in
                                  (match uu____80341 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80450 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80450 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80486 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80495 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80495
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80506 ->
                                                  let uu____80515 =
                                                    let uu____80523 =
                                                      get_vtok ()  in
                                                    (uu____80523, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80515
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80530 =
                                                let uu____80538 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80538)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80530
                                               in
                                            let uu____80552 =
                                              let vname_decl =
                                                let uu____80560 =
                                                  let uu____80572 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80572,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80560
                                                 in
                                              let uu____80583 =
                                                let env2 =
                                                  let uu___1026_80589 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80589.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80590 =
                                                  let uu____80592 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80592
                                                   in
                                                if uu____80590
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80583 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80609 =
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
                                                        let uu____80635 =
                                                          let uu____80638 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80638
                                                           in
                                                        let uu____80645 =
                                                          let uu____80646 =
                                                            let uu____80649 =
                                                              let uu____80650
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80650
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80654  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80654)
                                                              uu____80649
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80646
                                                           in
                                                        (uu____80635,
                                                          uu____80645)
                                                    | uu____80661 when
                                                        thunked ->
                                                        let uu____80672 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80672
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80687
                                                                 =
                                                                 let uu____80695
                                                                   =
                                                                   let uu____80698
                                                                    =
                                                                    let uu____80701
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80701]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80698
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80695)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80687
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80709
                                                               =
                                                               let uu____80717
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80717,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80709
                                                              in
                                                           let uu____80722 =
                                                             let uu____80725
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80725
                                                              in
                                                           (uu____80722,
                                                             env1))
                                                    | uu____80734 ->
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
                                                          let uu____80758 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80759 =
                                                            let uu____80770 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80770)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80758
                                                            uu____80759
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80780 =
                                                            let uu____80788 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80788,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80780
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
                                                            let uu____80799 =
                                                              let uu____80800
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80800]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80799
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80827 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80828 =
                                                              let uu____80839
                                                                =
                                                                let uu____80840
                                                                  =
                                                                  let uu____80845
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80846
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80845,
                                                                    uu____80846)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80840
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80839)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80827
                                                              uu____80828
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80875 =
                                                          let uu____80878 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80878
                                                           in
                                                        (uu____80875, env1)
                                                     in
                                                  (match uu____80609 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80899 =
                                                         let uu____80902 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80902
                                                           tok_decl
                                                          in
                                                       (uu____80899, env2))
                                               in
                                            (match uu____80552 with
                                             | (decls2,env2) ->
                                                 let uu____80921 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80931 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80931 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80946 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80946, decls)
                                                    in
                                                 (match uu____80921 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80961 =
                                                          let uu____80969 =
                                                            let uu____80970 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80971 =
                                                              let uu____80982
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80982)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80970
                                                              uu____80971
                                                             in
                                                          (uu____80969,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80961
                                                         in
                                                      let freshness =
                                                        let uu____80998 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80998
                                                        then
                                                          let uu____81006 =
                                                            let uu____81007 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____81008 =
                                                              let uu____81021
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____81028
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____81021,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____81028)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____81007
                                                              uu____81008
                                                             in
                                                          let uu____81034 =
                                                            let uu____81037 =
                                                              let uu____81038
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____81038
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____81037]  in
                                                          uu____81006 ::
                                                            uu____81034
                                                        else []  in
                                                      let g =
                                                        let uu____81044 =
                                                          let uu____81047 =
                                                            let uu____81050 =
                                                              let uu____81053
                                                                =
                                                                let uu____81056
                                                                  =
                                                                  let uu____81059
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____81059
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____81056
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____81053
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____81050
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____81047
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____81044
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
          let uu____81099 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____81099 with
          | FStar_Pervasives_Native.None  ->
              let uu____81110 = encode_free_var false env x t t_norm []  in
              (match uu____81110 with
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
            let uu____81173 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81173 with
            | (decls,env1) ->
                let uu____81184 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81184
                then
                  let uu____81191 =
                    let uu____81192 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81192  in
                  (uu____81191, env1)
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
             (fun uu____81248  ->
                fun lb  ->
                  match uu____81248 with
                  | (decls,env1) ->
                      let uu____81268 =
                        let uu____81273 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81273
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81268 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81302 = FStar_Syntax_Util.head_and_args t  in
    match uu____81302 with
    | (hd1,args) ->
        let uu____81346 =
          let uu____81347 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81347.FStar_Syntax_Syntax.n  in
        (match uu____81346 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81353,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81377 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81388 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81396 = en  in
    let uu____81397 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81396.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81396.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81396.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81396.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81396.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81396.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81396.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81396.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81396.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81396.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81397
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81427  ->
      fun quals  ->
        match uu____81427 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81532 = FStar_Util.first_N nbinders formals  in
              match uu____81532 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81633  ->
                         fun uu____81634  ->
                           match (uu____81633, uu____81634) with
                           | ((formal,uu____81660),(binder,uu____81662)) ->
                               let uu____81683 =
                                 let uu____81690 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81690)  in
                               FStar_Syntax_Syntax.NT uu____81683) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81704 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81745  ->
                              match uu____81745 with
                              | (x,i) ->
                                  let uu____81764 =
                                    let uu___1139_81765 = x  in
                                    let uu____81766 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81765.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81765.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81766
                                    }  in
                                  (uu____81764, i)))
                       in
                    FStar_All.pipe_right uu____81704
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81790 =
                      let uu____81795 = FStar_Syntax_Subst.compress body  in
                      let uu____81796 =
                        let uu____81797 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81797
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81795
                        uu____81796
                       in
                    uu____81790 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81848 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81848.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81848.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81848.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81848.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81848.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81848.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81848.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81848.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81848.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81848.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81848.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81848.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81848.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81848.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81848.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81848.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81848.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81848.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81848.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81848.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81848.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81848.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81848.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81848.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81848.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81848.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81848.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81848.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81848.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81848.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81848.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81848.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81848.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81848.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81848.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81848.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81848.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81848.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81848.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81848.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81848.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81848.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81920  ->
                       fun uu____81921  ->
                         match (uu____81920, uu____81921) with
                         | ((x,uu____81947),(b,uu____81949)) ->
                             let uu____81970 =
                               let uu____81977 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81977)  in
                             FStar_Syntax_Syntax.NT uu____81970) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____82002 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____82002
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____82031 ->
                    let uu____82038 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____82038
                | uu____82039 when Prims.op_Negation norm1 ->
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
                | uu____82042 ->
                    let uu____82043 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____82043)
                 in
              let aux t1 e1 =
                let uu____82085 = FStar_Syntax_Util.abs_formals e1  in
                match uu____82085 with
                | (binders,body,lopt) ->
                    let uu____82117 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82133 -> arrow_formals_comp_norm false t1  in
                    (match uu____82117 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82167 =
                           if nformals < nbinders
                           then
                             let uu____82211 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82211 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82295 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82295)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82335 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82335 with
                                | (binders1,body1) ->
                                    let uu____82388 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82388))
                             else
                               (let uu____82401 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82401))
                            in
                         (match uu____82167 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82461 = aux t e  in
              match uu____82461 with
              | (binders,body,comp) ->
                  let uu____82507 =
                    let uu____82518 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82518
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82533 = aux comp1 body1  in
                      match uu____82533 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82507 with
                   | (binders1,body1,comp1) ->
                       let uu____82616 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82616, comp1))
               in
            (try
               (fun uu___1216_82643  ->
                  match () with
                  | () ->
                      let uu____82650 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82650
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82666 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82729  ->
                                   fun lb  ->
                                     match uu____82729 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82784 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82784
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82790 =
                                             let uu____82799 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82799
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82790 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82666 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82940;
                                    FStar_Syntax_Syntax.lbeff = uu____82941;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82943;
                                    FStar_Syntax_Syntax.lbpos = uu____82944;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82968 =
                                     let uu____82975 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82975 with
                                     | (tcenv',uu____82991,e_t) ->
                                         let uu____82997 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____83008 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82997 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_83025 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_83025.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82968 with
                                    | (env',e1,t_norm1) ->
                                        let uu____83035 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____83035 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____83055 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____83055
                                               then
                                                 let uu____83060 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____83063 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____83060 uu____83063
                                               else ());
                                              (let uu____83068 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____83068 with
                                               | (vars,_guards,env'1,binder_decls,uu____83095)
                                                   ->
                                                   let uu____83108 =
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
                                                         let uu____83125 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83125
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83147 =
                                                          let uu____83148 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83149 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83148 fvb
                                                            uu____83149
                                                           in
                                                        (vars, uu____83147))
                                                      in
                                                   (match uu____83108 with
                                                    | (vars1,app) ->
                                                        let uu____83160 =
                                                          let is_logical =
                                                            let uu____83173 =
                                                              let uu____83174
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83174.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83173
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83180 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83184 =
                                                              let uu____83185
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83185
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83184
                                                              (fun lid  ->
                                                                 let uu____83194
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83194
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83195 =
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
                                                          if uu____83195
                                                          then
                                                            let uu____83211 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83212 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83211,
                                                              uu____83212)
                                                          else
                                                            (let uu____83223
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83223))
                                                           in
                                                        (match uu____83160
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83247
                                                                 =
                                                                 let uu____83255
                                                                   =
                                                                   let uu____83256
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83257
                                                                    =
                                                                    let uu____83268
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83268)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83256
                                                                    uu____83257
                                                                    in
                                                                 let uu____83277
                                                                   =
                                                                   let uu____83278
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83278
                                                                    in
                                                                 (uu____83255,
                                                                   uu____83277,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83247
                                                                in
                                                             let uu____83284
                                                               =
                                                               let uu____83287
                                                                 =
                                                                 let uu____83290
                                                                   =
                                                                   let uu____83293
                                                                    =
                                                                    let uu____83296
                                                                    =
                                                                    let uu____83299
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83299
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83296
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83293
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83290
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83287
                                                                in
                                                             (uu____83284,
                                                               env2)))))))
                               | uu____83308 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83368 =
                                   let uu____83374 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83374,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83368  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83380 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83433  ->
                                         fun fvb  ->
                                           match uu____83433 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83488 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83488
                                                  in
                                               let gtok =
                                                 let uu____83492 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83492
                                                  in
                                               let env4 =
                                                 let uu____83495 =
                                                   let uu____83498 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83504  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83504) uu____83498
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83495
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83380 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83624
                                     t_norm uu____83626 =
                                     match (uu____83624, uu____83626) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83656;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83657;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83659;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83660;_})
                                         ->
                                         let uu____83687 =
                                           let uu____83694 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83694 with
                                           | (tcenv',uu____83710,e_t) ->
                                               let uu____83716 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83727 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83716 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83744 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83744.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83687 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83757 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83757
                                                then
                                                  let uu____83762 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83764 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83766 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83762 uu____83764
                                                    uu____83766
                                                else ());
                                               (let uu____83771 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83771 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83798 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83798 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83820 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83820
                                                           then
                                                             let uu____83825
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83827
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83830
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83832
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83825
                                                               uu____83827
                                                               uu____83830
                                                               uu____83832
                                                           else ());
                                                          (let uu____83837 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83837
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83866)
                                                               ->
                                                               let uu____83879
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83892,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83896
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83896
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83909
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83909,
                                                                    decls0))
                                                                  in
                                                               (match uu____83879
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
                                                                    let uu____83930
                                                                    =
                                                                    let uu____83942
                                                                    =
                                                                    let uu____83945
                                                                    =
                                                                    let uu____83948
                                                                    =
                                                                    let uu____83951
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83951
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83948
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83945
                                                                     in
                                                                    (g,
                                                                    uu____83942,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83930
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
                                                                    let uu____83981
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83981
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
                                                                    let uu____83996
                                                                    =
                                                                    let uu____83999
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83999
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83996
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____84005
                                                                    =
                                                                    let uu____84008
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____84008
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84005
                                                                     in
                                                                    let uu____84013
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____84013
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____84029
                                                                    =
                                                                    let uu____84037
                                                                    =
                                                                    let uu____84038
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84039
                                                                    =
                                                                    let uu____84055
                                                                    =
                                                                    let uu____84056
                                                                    =
                                                                    let uu____84061
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____84061)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84056
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84055)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____84038
                                                                    uu____84039
                                                                     in
                                                                    let uu____84075
                                                                    =
                                                                    let uu____84076
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84076
                                                                     in
                                                                    (uu____84037,
                                                                    uu____84075,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84029
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____84083
                                                                    =
                                                                    let uu____84091
                                                                    =
                                                                    let uu____84092
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84093
                                                                    =
                                                                    let uu____84104
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84104)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84092
                                                                    uu____84093
                                                                     in
                                                                    (uu____84091,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84083
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84118
                                                                    =
                                                                    let uu____84126
                                                                    =
                                                                    let uu____84127
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84128
                                                                    =
                                                                    let uu____84139
                                                                    =
                                                                    let uu____84140
                                                                    =
                                                                    let uu____84145
                                                                    =
                                                                    let uu____84146
                                                                    =
                                                                    let uu____84149
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84149
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84146
                                                                     in
                                                                    (gsapp,
                                                                    uu____84145)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84140
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84139)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84127
                                                                    uu____84128
                                                                     in
                                                                    (uu____84126,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84118
                                                                     in
                                                                    let uu____84163
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
                                                                    let uu____84175
                                                                    =
                                                                    let uu____84176
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84176
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84175
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84178
                                                                    =
                                                                    let uu____84186
                                                                    =
                                                                    let uu____84187
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84188
                                                                    =
                                                                    let uu____84199
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84199)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84187
                                                                    uu____84188
                                                                     in
                                                                    (uu____84186,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84178
                                                                     in
                                                                    let uu____84212
                                                                    =
                                                                    let uu____84221
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84221
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84236
                                                                    =
                                                                    let uu____84239
                                                                    =
                                                                    let uu____84240
                                                                    =
                                                                    let uu____84248
                                                                    =
                                                                    let uu____84249
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84250
                                                                    =
                                                                    let uu____84261
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84261)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84249
                                                                    uu____84250
                                                                     in
                                                                    (uu____84248,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84240
                                                                     in
                                                                    [uu____84239]
                                                                     in
                                                                    (d3,
                                                                    uu____84236)
                                                                     in
                                                                    match uu____84212
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84163
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84318
                                                                    =
                                                                    let uu____84321
                                                                    =
                                                                    let uu____84324
                                                                    =
                                                                    let uu____84327
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84327
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84324
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84321
                                                                     in
                                                                    let uu____84334
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84318,
                                                                    uu____84334,
                                                                    env02))))))))))
                                      in
                                   let uu____84339 =
                                     let uu____84352 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84415  ->
                                          fun uu____84416  ->
                                            match (uu____84415, uu____84416)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84541 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84541 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84352
                                      in
                                   (match uu____84339 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84608 =
                                          let isDeclFun uu___640_84625 =
                                            match uu___640_84625 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84627 -> true
                                            | uu____84640 -> false  in
                                          let uu____84642 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84642
                                            (fun decls3  ->
                                               let uu____84672 =
                                                 FStar_List.fold_left
                                                   (fun uu____84703  ->
                                                      fun elt  ->
                                                        match uu____84703
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84744 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84744
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84772
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84772
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
                                                                    let uu___1459_84810
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84810.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84810.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84810.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84672 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84842 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84842, elts, rest))
                                           in
                                        (match uu____84608 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84871 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84877  ->
                                        match uu___641_84877 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84880 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84888 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84888)))
                                in
                             if uu____84871
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84910  ->
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
                   let uu____84949 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84949
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84968 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84968, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____85024 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____85024 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____85030 = encode_sigelt' env se  in
      match uu____85030 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____85042 =
                  let uu____85045 =
                    let uu____85046 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____85046  in
                  [uu____85045]  in
                FStar_All.pipe_right uu____85042
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____85051 ->
                let uu____85052 =
                  let uu____85055 =
                    let uu____85058 =
                      let uu____85059 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____85059  in
                    [uu____85058]  in
                  FStar_All.pipe_right uu____85055
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____85066 =
                  let uu____85069 =
                    let uu____85072 =
                      let uu____85075 =
                        let uu____85076 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____85076  in
                      [uu____85075]  in
                    FStar_All.pipe_right uu____85072
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____85069  in
                FStar_List.append uu____85052 uu____85066
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____85090 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____85090
       then
         let uu____85095 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____85095
       else ());
      (let is_opaque_to_smt t =
         let uu____85107 =
           let uu____85108 = FStar_Syntax_Subst.compress t  in
           uu____85108.FStar_Syntax_Syntax.n  in
         match uu____85107 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85113)) -> s = "opaque_to_smt"
         | uu____85118 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85127 =
           let uu____85128 = FStar_Syntax_Subst.compress t  in
           uu____85128.FStar_Syntax_Syntax.n  in
         match uu____85127 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85133)) -> s = "uninterpreted_by_smt"
         | uu____85138 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85144 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85150 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85162 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85163 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85164 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85177 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85179 =
             let uu____85181 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85181  in
           if uu____85179
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85210 ->
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
                let uu____85242 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85242 with
                | (formals,uu____85262) ->
                    let arity = FStar_List.length formals  in
                    let uu____85286 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85286 with
                     | (aname,atok,env2) ->
                         let uu____85312 =
                           let uu____85317 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85317 env2
                            in
                         (match uu____85312 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85329 =
                                  let uu____85330 =
                                    let uu____85342 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85362  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85342,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85330
                                   in
                                [uu____85329;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85379 =
                                let aux uu____85425 uu____85426 =
                                  match (uu____85425, uu____85426) with
                                  | ((bv,uu____85470),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85502 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85502 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85525 =
                                             let uu____85528 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85528 :: acc_sorts  in
                                           (env4, uu____85525, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85379 with
                               | (uu____85560,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85576 =
                                       let uu____85584 =
                                         let uu____85585 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85586 =
                                           let uu____85597 =
                                             let uu____85598 =
                                               let uu____85603 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85603)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85598
                                              in
                                           ([[app]], xs_sorts, uu____85597)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85585 uu____85586
                                          in
                                       (uu____85584,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85576
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85618 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85618
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85621 =
                                       let uu____85629 =
                                         let uu____85630 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85631 =
                                           let uu____85642 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85642)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85630 uu____85631
                                          in
                                       (uu____85629,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85621
                                      in
                                   let uu____85655 =
                                     let uu____85658 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85658  in
                                   (env2, uu____85655))))
                 in
              let uu____85667 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85667 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85693,uu____85694)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85695 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85695 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85717,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85724 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85730  ->
                       match uu___642_85730 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85733 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85739 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85742 -> false))
                in
             Prims.op_Negation uu____85724  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85752 =
                let uu____85757 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85757 env fv t quals  in
              match uu____85752 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85771 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85771  in
                  let uu____85774 =
                    let uu____85775 =
                      let uu____85778 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85778
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85775  in
                  (uu____85774, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85788 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85788 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85800 = env  in
                  let uu____85801 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85800.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85800.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85800.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85801;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85800.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85800.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85800.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85800.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85800.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85800.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85800.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85803 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85803 with
                 | (f3,decls) ->
                     let g =
                       let uu____85817 =
                         let uu____85820 =
                           let uu____85821 =
                             let uu____85829 =
                               let uu____85830 =
                                 let uu____85832 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85832
                                  in
                               FStar_Pervasives_Native.Some uu____85830  in
                             let uu____85836 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85829, uu____85836)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85821  in
                         [uu____85820]  in
                       FStar_All.pipe_right uu____85817
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85845) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85859 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85881 =
                        let uu____85884 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85884.FStar_Syntax_Syntax.fv_name  in
                      uu____85881.FStar_Syntax_Syntax.v  in
                    let uu____85885 =
                      let uu____85887 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85887  in
                    if uu____85885
                    then
                      let val_decl =
                        let uu___1629_85919 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85919.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85919.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85919.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85920 = encode_sigelt' env1 val_decl  in
                      match uu____85920 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85859 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85956,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85958;
                           FStar_Syntax_Syntax.lbtyp = uu____85959;
                           FStar_Syntax_Syntax.lbeff = uu____85960;
                           FStar_Syntax_Syntax.lbdef = uu____85961;
                           FStar_Syntax_Syntax.lbattrs = uu____85962;
                           FStar_Syntax_Syntax.lbpos = uu____85963;_}::[]),uu____85964)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85983 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85983 with
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
                  let uu____86021 =
                    let uu____86024 =
                      let uu____86025 =
                        let uu____86033 =
                          let uu____86034 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____86035 =
                            let uu____86046 =
                              let uu____86047 =
                                let uu____86052 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____86052)  in
                              FStar_SMTEncoding_Util.mkEq uu____86047  in
                            ([[b2t_x]], [xx], uu____86046)  in
                          FStar_SMTEncoding_Term.mkForall uu____86034
                            uu____86035
                           in
                        (uu____86033,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____86025  in
                    [uu____86024]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____86021
                   in
                let uu____86090 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____86090, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____86093,uu____86094) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86104  ->
                   match uu___643_86104 with
                   | FStar_Syntax_Syntax.Discriminator uu____86106 -> true
                   | uu____86108 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86110,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86122 =
                      let uu____86124 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86124.FStar_Ident.idText  in
                    uu____86122 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86131  ->
                      match uu___644_86131 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86134 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86137) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86151  ->
                   match uu___645_86151 with
                   | FStar_Syntax_Syntax.Projector uu____86153 -> true
                   | uu____86159 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86163 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86163 with
            | FStar_Pervasives_Native.Some uu____86170 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86172 = se  in
                  let uu____86173 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86173;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86172.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86172.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86172.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86176) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86191) ->
           let uu____86200 = encode_sigelts env ses  in
           (match uu____86200 with
            | (g,env1) ->
                let uu____86211 =
                  FStar_List.fold_left
                    (fun uu____86235  ->
                       fun elt  ->
                         match uu____86235 with
                         | (g',inversions) ->
                             let uu____86263 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86286  ->
                                       match uu___646_86286 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86288;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86289;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86290;_}
                                           -> false
                                       | uu____86297 -> true))
                                in
                             (match uu____86263 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86322 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86322.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86322.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86322.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86211 with
                 | (g',inversions) ->
                     let uu____86341 =
                       FStar_List.fold_left
                         (fun uu____86372  ->
                            fun elt  ->
                              match uu____86372 with
                              | (decls,elts,rest) ->
                                  let uu____86413 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86422  ->
                                            match uu___647_86422 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86424 -> true
                                            | uu____86437 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86413
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86460 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86481  ->
                                               match uu___648_86481 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86483 -> true
                                               | uu____86496 -> false))
                                        in
                                     match uu____86460 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86527 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86527.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86527.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86527.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86341 with
                      | (decls,elts,rest) ->
                          let uu____86553 =
                            let uu____86554 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86561 =
                              let uu____86564 =
                                let uu____86567 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86567  in
                              FStar_List.append elts uu____86564  in
                            FStar_List.append uu____86554 uu____86561  in
                          (uu____86553, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86578,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86591 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86591 with
             | (usubst,uvs) ->
                 let uu____86611 =
                   let uu____86618 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86619 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86620 =
                     let uu____86621 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86621 k  in
                   (uu____86618, uu____86619, uu____86620)  in
                 (match uu____86611 with
                  | (env1,tps1,k1) ->
                      let uu____86634 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86634 with
                       | (tps2,k2) ->
                           let uu____86642 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86642 with
                            | (uu____86658,k3) ->
                                let uu____86680 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86680 with
                                 | (tps3,env_tps,uu____86692,us) ->
                                     let u_k =
                                       let uu____86695 =
                                         let uu____86696 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86697 =
                                           let uu____86702 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86704 =
                                             let uu____86705 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86705
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86702 uu____86704
                                            in
                                         uu____86697
                                           FStar_Pervasives_Native.None
                                           uu____86696
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86695 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86725) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86731,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86734) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86742,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86749) ->
                                           let uu____86750 =
                                             let uu____86752 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86752
                                              in
                                           failwith uu____86750
                                       | (uu____86756,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86757 =
                                             let uu____86759 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86759
                                              in
                                           failwith uu____86757
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86763,uu____86764) ->
                                           let uu____86773 =
                                             let uu____86775 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86775
                                              in
                                           failwith uu____86773
                                       | (uu____86779,FStar_Syntax_Syntax.U_unif
                                          uu____86780) ->
                                           let uu____86789 =
                                             let uu____86791 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86791
                                              in
                                           failwith uu____86789
                                       | uu____86795 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86808 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86808 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86826 = u_leq_u_k u_tp  in
                                       if uu____86826
                                       then true
                                       else
                                         (let uu____86833 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86833 with
                                          | (formals,uu____86850) ->
                                              let uu____86871 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86871 with
                                               | (uu____86881,uu____86882,uu____86883,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86894 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86894
             then
               let uu____86899 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86899
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86919  ->
                       match uu___649_86919 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86923 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86936 = c  in
                 match uu____86936 with
                 | (name,args,uu____86941,uu____86942,uu____86943) ->
                     let uu____86954 =
                       let uu____86955 =
                         let uu____86967 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86994  ->
                                   match uu____86994 with
                                   | (uu____87003,sort,uu____87005) -> sort))
                            in
                         (name, uu____86967,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86955  in
                     [uu____86954]
               else
                 (let uu____87016 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____87016 c)
                in
             let inversion_axioms tapp vars =
               let uu____87034 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____87042 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____87042 FStar_Option.isNone))
                  in
               if uu____87034
               then []
               else
                 (let uu____87077 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____87077 with
                  | (xxsym,xx) ->
                      let uu____87090 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87129  ->
                                fun l  ->
                                  match uu____87129 with
                                  | (out,decls) ->
                                      let uu____87149 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87149 with
                                       | (uu____87160,data_t) ->
                                           let uu____87162 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87162 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87206 =
                                                    let uu____87207 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87207.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87206 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87210,indices)
                                                      -> indices
                                                  | uu____87236 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87266  ->
                                                            match uu____87266
                                                            with
                                                            | (x,uu____87274)
                                                                ->
                                                                let uu____87279
                                                                  =
                                                                  let uu____87280
                                                                    =
                                                                    let uu____87288
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87288,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87280
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87279)
                                                       env)
                                                   in
                                                let uu____87293 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87293 with
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
                                                                  let uu____87328
                                                                    =
                                                                    let uu____87333
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87333,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87328)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87336 =
                                                         let uu____87337 =
                                                           let uu____87342 =
                                                             let uu____87343
                                                               =
                                                               let uu____87348
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87349
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87348,
                                                                 uu____87349)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87343
                                                              in
                                                           (out, uu____87342)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87337
                                                          in
                                                       (uu____87336,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____87090 with
                       | (data_ax,decls) ->
                           let uu____87364 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87364 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87381 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87381 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87388 =
                                    let uu____87396 =
                                      let uu____87397 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87398 =
                                        let uu____87409 =
                                          let uu____87410 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87412 =
                                            let uu____87415 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87415 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87410 uu____87412
                                           in
                                        let uu____87417 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87409,
                                          uu____87417)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87397 uu____87398
                                       in
                                    let uu____87426 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87396,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87426)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87388
                                   in
                                let uu____87432 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87432)))
                in
             let uu____87439 =
               let uu____87444 =
                 let uu____87445 = FStar_Syntax_Subst.compress k  in
                 uu____87445.FStar_Syntax_Syntax.n  in
               match uu____87444 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87480 -> (tps, k)  in
             match uu____87439 with
             | (formals,res) ->
                 let uu____87487 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87487 with
                  | (formals1,res1) ->
                      let uu____87498 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87498 with
                       | (vars,guards,env',binder_decls,uu____87523) ->
                           let arity = FStar_List.length vars  in
                           let uu____87537 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87537 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87567 =
                                    let uu____87575 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87575)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87567
                                   in
                                let uu____87581 =
                                  let tname_decl =
                                    let uu____87591 =
                                      let uu____87592 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87611 =
                                                  let uu____87613 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87613
                                                   in
                                                let uu____87615 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87611, uu____87615,
                                                  false)))
                                         in
                                      let uu____87619 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87592,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87619, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87591
                                     in
                                  let uu____87627 =
                                    match vars with
                                    | [] ->
                                        let uu____87640 =
                                          let uu____87641 =
                                            let uu____87644 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87650  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87650) uu____87644
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87641
                                           in
                                        ([], uu____87640)
                                    | uu____87657 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87667 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87667
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87683 =
                                            let uu____87691 =
                                              let uu____87692 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87693 =
                                                let uu____87709 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87709)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87692 uu____87693
                                               in
                                            (uu____87691,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87683
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87627 with
                                  | (tok_decls,env2) ->
                                      let uu____87736 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87736
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87581 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87764 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87764 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87786 =
                                                 let uu____87787 =
                                                   let uu____87795 =
                                                     let uu____87796 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87796
                                                      in
                                                   (uu____87795,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87787
                                                  in
                                               [uu____87786]
                                             else []  in
                                           let uu____87804 =
                                             let uu____87807 =
                                               let uu____87810 =
                                                 let uu____87813 =
                                                   let uu____87814 =
                                                     let uu____87822 =
                                                       let uu____87823 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87824 =
                                                         let uu____87835 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87835)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87823
                                                         uu____87824
                                                        in
                                                     (uu____87822,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87814
                                                    in
                                                 [uu____87813]  in
                                               FStar_List.append karr
                                                 uu____87810
                                                in
                                             FStar_All.pipe_right uu____87807
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87804
                                        in
                                     let aux =
                                       let uu____87854 =
                                         let uu____87857 =
                                           inversion_axioms tapp vars  in
                                         let uu____87860 =
                                           let uu____87863 =
                                             let uu____87866 =
                                               let uu____87867 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87867 env2
                                                 tapp vars
                                                in
                                             [uu____87866]  in
                                           FStar_All.pipe_right uu____87863
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87857
                                           uu____87860
                                          in
                                       FStar_List.append kindingAx
                                         uu____87854
                                        in
                                     let g =
                                       let uu____87875 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87875
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87883,uu____87884,uu____87885,uu____87886,uu____87887)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87895,t,uu____87897,n_tps,uu____87899) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87909 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87909 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87957 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87957 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87985 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87985 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____88005 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____88005 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____88084 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____88084,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____88091 =
                                   let uu____88092 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____88092, true)
                                    in
                                 let uu____88100 =
                                   let uu____88107 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88107
                                    in
                                 FStar_All.pipe_right uu____88091 uu____88100
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
                               let uu____88119 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88119 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88131::uu____88132 ->
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
                                            let uu____88181 =
                                              let uu____88182 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88182]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88181
                                             in
                                          let uu____88208 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88209 =
                                            let uu____88220 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88220)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88208 uu____88209
                                      | uu____88247 -> tok_typing  in
                                    let uu____88258 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88258 with
                                     | (vars',guards',env'',decls_formals,uu____88283)
                                         ->
                                         let uu____88296 =
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
                                         (match uu____88296 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88326 ->
                                                    let uu____88335 =
                                                      let uu____88336 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88336
                                                       in
                                                    [uu____88335]
                                                 in
                                              let encode_elim uu____88352 =
                                                let uu____88353 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88353 with
                                                | (head1,args) ->
                                                    let uu____88404 =
                                                      let uu____88405 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88405.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88404 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88417;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88418;_},uu____88419)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88425 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88425
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
                                                                  | uu____88488
                                                                    ->
                                                                    let uu____88489
                                                                    =
                                                                    let uu____88495
                                                                    =
                                                                    let uu____88497
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88497
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88495)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88489
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88520
                                                                    =
                                                                    let uu____88522
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88522
                                                                     in
                                                                    if
                                                                    uu____88520
                                                                    then
                                                                    let uu____88544
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88544]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88547
                                                                =
                                                                let uu____88561
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88618
                                                                     ->
                                                                    fun
                                                                    uu____88619
                                                                     ->
                                                                    match 
                                                                    (uu____88618,
                                                                    uu____88619)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88730
                                                                    =
                                                                    let uu____88738
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88738
                                                                     in
                                                                    (match uu____88730
                                                                    with
                                                                    | 
                                                                    (uu____88752,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88763
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88763
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88768
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88768
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
                                                                  uu____88561
                                                                 in
                                                              (match uu____88547
                                                               with
                                                               | (uu____88789,arg_vars,elim_eqns_or_guards,uu____88792)
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
                                                                    let uu____88819
                                                                    =
                                                                    let uu____88827
                                                                    =
                                                                    let uu____88828
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88829
                                                                    =
                                                                    let uu____88840
                                                                    =
                                                                    let uu____88841
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88841
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88843
                                                                    =
                                                                    let uu____88844
                                                                    =
                                                                    let uu____88849
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88849)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88844
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88840,
                                                                    uu____88843)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88828
                                                                    uu____88829
                                                                     in
                                                                    (uu____88827,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88819
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88864
                                                                    =
                                                                    let uu____88865
                                                                    =
                                                                    let uu____88871
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88871,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88865
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88864
                                                                     in
                                                                    let uu____88874
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88874
                                                                    then
                                                                    let x =
                                                                    let uu____88878
                                                                    =
                                                                    let uu____88884
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88884,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88878
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88889
                                                                    =
                                                                    let uu____88897
                                                                    =
                                                                    let uu____88898
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88899
                                                                    =
                                                                    let uu____88910
                                                                    =
                                                                    let uu____88915
                                                                    =
                                                                    let uu____88918
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88918]
                                                                     in
                                                                    [uu____88915]
                                                                     in
                                                                    let uu____88923
                                                                    =
                                                                    let uu____88924
                                                                    =
                                                                    let uu____88929
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88929,
                                                                    uu____88931)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88924
                                                                     in
                                                                    (uu____88910,
                                                                    [x],
                                                                    uu____88923)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88898
                                                                    uu____88899
                                                                     in
                                                                    let uu____88952
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88897,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88952)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88889
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88963
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
                                                                    (let uu____88986
                                                                    =
                                                                    let uu____88987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88987
                                                                    dapp1  in
                                                                    [uu____88986])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88963
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88994
                                                                    =
                                                                    let uu____89002
                                                                    =
                                                                    let uu____89003
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89004
                                                                    =
                                                                    let uu____89015
                                                                    =
                                                                    let uu____89016
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89016
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89018
                                                                    =
                                                                    let uu____89019
                                                                    =
                                                                    let uu____89024
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89024)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89019
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89015,
                                                                    uu____89018)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89003
                                                                    uu____89004
                                                                     in
                                                                    (uu____89002,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88994)
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
                                                         let uu____89043 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____89043
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
                                                                  | uu____89106
                                                                    ->
                                                                    let uu____89107
                                                                    =
                                                                    let uu____89113
                                                                    =
                                                                    let uu____89115
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89115
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89113)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89107
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89138
                                                                    =
                                                                    let uu____89140
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89140
                                                                     in
                                                                    if
                                                                    uu____89138
                                                                    then
                                                                    let uu____89162
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89162]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89165
                                                                =
                                                                let uu____89179
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89236
                                                                     ->
                                                                    fun
                                                                    uu____89237
                                                                     ->
                                                                    match 
                                                                    (uu____89236,
                                                                    uu____89237)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89348
                                                                    =
                                                                    let uu____89356
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89356
                                                                     in
                                                                    (match uu____89348
                                                                    with
                                                                    | 
                                                                    (uu____89370,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89381
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89381
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89386
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89386
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
                                                                  uu____89179
                                                                 in
                                                              (match uu____89165
                                                               with
                                                               | (uu____89407,arg_vars,elim_eqns_or_guards,uu____89410)
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
                                                                    let uu____89437
                                                                    =
                                                                    let uu____89445
                                                                    =
                                                                    let uu____89446
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89447
                                                                    =
                                                                    let uu____89458
                                                                    =
                                                                    let uu____89459
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89459
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89461
                                                                    =
                                                                    let uu____89462
                                                                    =
                                                                    let uu____89467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89467)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89462
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89458,
                                                                    uu____89461)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89446
                                                                    uu____89447
                                                                     in
                                                                    (uu____89445,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89437
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89482
                                                                    =
                                                                    let uu____89483
                                                                    =
                                                                    let uu____89489
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89489,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89483
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89482
                                                                     in
                                                                    let uu____89492
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89492
                                                                    then
                                                                    let x =
                                                                    let uu____89496
                                                                    =
                                                                    let uu____89502
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89502,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89496
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89507
                                                                    =
                                                                    let uu____89515
                                                                    =
                                                                    let uu____89516
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89517
                                                                    =
                                                                    let uu____89528
                                                                    =
                                                                    let uu____89533
                                                                    =
                                                                    let uu____89536
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89536]
                                                                     in
                                                                    [uu____89533]
                                                                     in
                                                                    let uu____89541
                                                                    =
                                                                    let uu____89542
                                                                    =
                                                                    let uu____89547
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89549
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89547,
                                                                    uu____89549)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89542
                                                                     in
                                                                    (uu____89528,
                                                                    [x],
                                                                    uu____89541)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89516
                                                                    uu____89517
                                                                     in
                                                                    let uu____89570
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89515,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89570)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89507
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89581
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
                                                                    (let uu____89604
                                                                    =
                                                                    let uu____89605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89605
                                                                    dapp1  in
                                                                    [uu____89604])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89581
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89612
                                                                    =
                                                                    let uu____89620
                                                                    =
                                                                    let uu____89621
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89622
                                                                    =
                                                                    let uu____89633
                                                                    =
                                                                    let uu____89634
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89634
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89636
                                                                    =
                                                                    let uu____89637
                                                                    =
                                                                    let uu____89642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89642)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89637
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89633,
                                                                    uu____89636)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89621
                                                                    uu____89622
                                                                     in
                                                                    (uu____89620,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89612)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89659 ->
                                                         ((let uu____89661 =
                                                             let uu____89667
                                                               =
                                                               let uu____89669
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89671
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89669
                                                                 uu____89671
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89667)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89661);
                                                          ([], [])))
                                                 in
                                              let uu____89679 =
                                                encode_elim ()  in
                                              (match uu____89679 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89705 =
                                                       let uu____89708 =
                                                         let uu____89711 =
                                                           let uu____89714 =
                                                             let uu____89717
                                                               =
                                                               let uu____89720
                                                                 =
                                                                 let uu____89723
                                                                   =
                                                                   let uu____89724
                                                                    =
                                                                    let uu____89736
                                                                    =
                                                                    let uu____89737
                                                                    =
                                                                    let uu____89739
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89739
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89737
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89736)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89724
                                                                    in
                                                                 [uu____89723]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89720
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89717
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89750 =
                                                             let uu____89753
                                                               =
                                                               let uu____89756
                                                                 =
                                                                 let uu____89759
                                                                   =
                                                                   let uu____89762
                                                                    =
                                                                    let uu____89765
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89770
                                                                    =
                                                                    let uu____89773
                                                                    =
                                                                    let uu____89774
                                                                    =
                                                                    let uu____89782
                                                                    =
                                                                    let uu____89783
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89784
                                                                    =
                                                                    let uu____89795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89795)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89783
                                                                    uu____89784
                                                                     in
                                                                    (uu____89782,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89774
                                                                     in
                                                                    let uu____89808
                                                                    =
                                                                    let uu____89811
                                                                    =
                                                                    let uu____89812
                                                                    =
                                                                    let uu____89820
                                                                    =
                                                                    let uu____89821
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89822
                                                                    =
                                                                    let uu____89833
                                                                    =
                                                                    let uu____89834
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89834
                                                                    vars'  in
                                                                    let uu____89836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89833,
                                                                    uu____89836)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89821
                                                                    uu____89822
                                                                     in
                                                                    (uu____89820,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89812
                                                                     in
                                                                    [uu____89811]
                                                                     in
                                                                    uu____89773
                                                                    ::
                                                                    uu____89808
                                                                     in
                                                                    uu____89765
                                                                    ::
                                                                    uu____89770
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89762
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89759
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89756
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89753
                                                              in
                                                           FStar_List.append
                                                             uu____89714
                                                             uu____89750
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89711
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89708
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89705
                                                      in
                                                   let uu____89853 =
                                                     let uu____89854 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89854 g
                                                      in
                                                   (uu____89853, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89888  ->
              fun se  ->
                match uu____89888 with
                | (g,env1) ->
                    let uu____89908 = encode_sigelt env1 se  in
                    (match uu____89908 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89976 =
        match uu____89976 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____90013 ->
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
                 ((let uu____90021 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____90021
                   then
                     let uu____90026 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____90028 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____90030 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____90026 uu____90028 uu____90030
                   else ());
                  (let uu____90035 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____90035 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____90053 =
                         let uu____90061 =
                           let uu____90063 =
                             let uu____90065 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____90065
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____90063  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____90061
                          in
                       (match uu____90053 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____90085 = FStar_Options.log_queries ()
                                 in
                              if uu____90085
                              then
                                let uu____90088 =
                                  let uu____90090 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____90092 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____90094 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____90090 uu____90092 uu____90094
                                   in
                                FStar_Pervasives_Native.Some uu____90088
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90110 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90120 =
                                let uu____90123 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90123  in
                              FStar_List.append uu____90110 uu____90120  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90135,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90155 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90155 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90176 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90176 with | (uu____90203,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90256  ->
              match uu____90256 with
              | (l,uu____90265,uu____90266) ->
                  let uu____90269 =
                    let uu____90281 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90281, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90269))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90314  ->
              match uu____90314 with
              | (l,uu____90325,uu____90326) ->
                  let uu____90329 =
                    let uu____90330 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90333  -> FStar_SMTEncoding_Term.Echo _90333)
                      uu____90330
                     in
                  let uu____90334 =
                    let uu____90337 =
                      let uu____90338 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90338  in
                    [uu____90337]  in
                  uu____90329 :: uu____90334))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90367 =
      let uu____90370 =
        let uu____90371 = FStar_Util.psmap_empty ()  in
        let uu____90386 =
          let uu____90395 = FStar_Util.psmap_empty ()  in (uu____90395, [])
           in
        let uu____90402 =
          let uu____90404 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90404 FStar_Ident.string_of_lid  in
        let uu____90406 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90371;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90386;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90402;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90406
        }  in
      [uu____90370]  in
    FStar_ST.op_Colon_Equals last_env uu____90367
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90450 = FStar_ST.op_Bang last_env  in
      match uu____90450 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90478 ->
          let uu___2175_90481 = e  in
          let uu____90482 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90481.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90481.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90481.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90481.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90481.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90481.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90481.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90482;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90481.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90481.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90490 = FStar_ST.op_Bang last_env  in
    match uu____90490 with
    | [] -> failwith "Empty env stack"
    | uu____90517::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90549  ->
    let uu____90550 = FStar_ST.op_Bang last_env  in
    match uu____90550 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90610  ->
    let uu____90611 = FStar_ST.op_Bang last_env  in
    match uu____90611 with
    | [] -> failwith "Popping an empty stack"
    | uu____90638::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90675  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90728  ->
         let uu____90729 = snapshot_env ()  in
         match uu____90729 with
         | (env_depth,()) ->
             let uu____90751 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90751 with
              | (varops_depth,()) ->
                  let uu____90773 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90773 with
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
        (fun uu____90831  ->
           let uu____90832 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90832 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90927 = snapshot msg  in () 
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
        | (uu____90973::uu____90974,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90982 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90982.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90982.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90982.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90983 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_91010 = elt  in
        let uu____91011 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_91010.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_91010.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____91011;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_91010.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____91031 =
        let uu____91034 =
          let uu____91035 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____91035  in
        let uu____91036 = open_fact_db_tags env  in uu____91034 ::
          uu____91036
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____91031
  
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
      let uu____91063 = encode_sigelt env se  in
      match uu____91063 with
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
                (let uu____91109 =
                   let uu____91112 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91112
                    in
                 match uu____91109 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91127 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91127
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91157 = FStar_Options.log_queries ()  in
        if uu____91157
        then
          let uu____91162 =
            let uu____91163 =
              let uu____91165 =
                let uu____91167 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91167 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91165  in
            FStar_SMTEncoding_Term.Caption uu____91163  in
          uu____91162 :: decls
        else decls  in
      (let uu____91186 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91186
       then
         let uu____91189 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91189
       else ());
      (let env =
         let uu____91195 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91195 tcenv  in
       let uu____91196 = encode_top_level_facts env se  in
       match uu____91196 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91210 =
               let uu____91213 =
                 let uu____91216 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91216
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91213  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91210)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91249 = FStar_Options.log_queries ()  in
          if uu____91249
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91269 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91269.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91269.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91269.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91269.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91269.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91269.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91269.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91269.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91269.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91269.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91274 =
             let uu____91277 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91277
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91274  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91297 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91297
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
          (let uu____91321 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91321
           then
             let uu____91324 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91324
           else ());
          (let env =
             let uu____91332 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91332
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91371  ->
                     fun se  ->
                       match uu____91371 with
                       | (g,env2) ->
                           let uu____91391 = encode_top_level_facts env2 se
                              in
                           (match uu____91391 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91414 =
             encode_signature
               (let uu___2303_91423 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91423.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91423.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91423.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91423.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91423.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91423.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91423.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91423.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91423.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91423.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91414 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91439 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91439
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91445 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91445))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91473  ->
        match uu____91473 with
        | (decls,fvbs) ->
            ((let uu____91487 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91487
              then ()
              else
                (let uu____91492 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91492
                 then
                   let uu____91495 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91495
                 else ()));
             (let env =
                let uu____91503 = get_env name tcenv  in
                FStar_All.pipe_right uu____91503
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91505 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91505
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91519 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91519
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
        (let uu____91581 =
           let uu____91583 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91583.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91581);
        (let env =
           let uu____91585 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91585 tcenv  in
         let uu____91586 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91625 = aux rest  in
                 (match uu____91625 with
                  | (out,rest1) ->
                      let t =
                        let uu____91653 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91653 with
                        | FStar_Pervasives_Native.Some uu____91656 ->
                            let uu____91657 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91657
                              x.FStar_Syntax_Syntax.sort
                        | uu____91658 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91662 =
                        let uu____91665 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91668 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91668.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91668.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91665 :: out  in
                      (uu____91662, rest1))
             | uu____91673 -> ([], bindings)  in
           let uu____91680 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91680 with
           | (closing,bindings) ->
               let uu____91707 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91707, bindings)
            in
         match uu____91586 with
         | (q1,bindings) ->
             let uu____91738 = encode_env_bindings env bindings  in
             (match uu____91738 with
              | (env_decls,env1) ->
                  ((let uu____91760 =
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
                    if uu____91760
                    then
                      let uu____91767 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91767
                    else ());
                   (let uu____91772 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91772 with
                    | (phi,qdecls) ->
                        let uu____91793 =
                          let uu____91798 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91798 phi
                           in
                        (match uu____91793 with
                         | (labels,phi1) ->
                             let uu____91815 = encode_labels labels  in
                             (match uu____91815 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91851 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91851
                                    then
                                      let uu____91856 =
                                        let uu____91857 =
                                          let uu____91859 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91859
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91857
                                         in
                                      [uu____91856]
                                    else []  in
                                  let query_prelude =
                                    let uu____91867 =
                                      let uu____91868 =
                                        let uu____91869 =
                                          let uu____91872 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91879 =
                                            let uu____91882 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91882
                                             in
                                          FStar_List.append uu____91872
                                            uu____91879
                                           in
                                        FStar_List.append env_decls
                                          uu____91869
                                         in
                                      FStar_All.pipe_right uu____91868
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91867
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91892 =
                                      let uu____91900 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91901 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91900,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91901)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91892
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
  