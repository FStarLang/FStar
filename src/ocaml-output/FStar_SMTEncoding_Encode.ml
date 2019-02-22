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
  let uu____71940 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____71940 with
  | (asym,a) ->
      let uu____71951 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____71951 with
       | (xsym,x) ->
           let uu____71962 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____71962 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72040 =
                      let uu____72052 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72052, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72040  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72072 =
                      let uu____72080 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72080)  in
                    FStar_SMTEncoding_Util.mkApp uu____72072  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____72099 =
                    let uu____72102 =
                      let uu____72105 =
                        let uu____72108 =
                          let uu____72109 =
                            let uu____72117 =
                              let uu____72118 =
                                let uu____72129 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____72129)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____72118
                               in
                            (uu____72117, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____72109  in
                        let uu____72141 =
                          let uu____72144 =
                            let uu____72145 =
                              let uu____72153 =
                                let uu____72154 =
                                  let uu____72165 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____72165)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____72154
                                 in
                              (uu____72153,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____72145  in
                          [uu____72144]  in
                        uu____72108 :: uu____72141  in
                      xtok_decl :: uu____72105  in
                    xname_decl :: uu____72102  in
                  (xtok1, (FStar_List.length vars), uu____72099)  in
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
                  let uu____72335 =
                    let uu____72356 =
                      let uu____72375 =
                        let uu____72376 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____72376
                         in
                      quant axy uu____72375  in
                    (FStar_Parser_Const.op_Eq, uu____72356)  in
                  let uu____72393 =
                    let uu____72416 =
                      let uu____72437 =
                        let uu____72456 =
                          let uu____72457 =
                            let uu____72458 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____72458  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____72457
                           in
                        quant axy uu____72456  in
                      (FStar_Parser_Const.op_notEq, uu____72437)  in
                    let uu____72475 =
                      let uu____72498 =
                        let uu____72519 =
                          let uu____72538 =
                            let uu____72539 =
                              let uu____72540 =
                                let uu____72545 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____72546 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____72545, uu____72546)  in
                              FStar_SMTEncoding_Util.mkAnd uu____72540  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____72539
                             in
                          quant xy uu____72538  in
                        (FStar_Parser_Const.op_And, uu____72519)  in
                      let uu____72563 =
                        let uu____72586 =
                          let uu____72607 =
                            let uu____72626 =
                              let uu____72627 =
                                let uu____72628 =
                                  let uu____72633 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____72634 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____72633, uu____72634)  in
                                FStar_SMTEncoding_Util.mkOr uu____72628  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____72627
                               in
                            quant xy uu____72626  in
                          (FStar_Parser_Const.op_Or, uu____72607)  in
                        let uu____72651 =
                          let uu____72674 =
                            let uu____72695 =
                              let uu____72714 =
                                let uu____72715 =
                                  let uu____72716 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____72716
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____72715
                                 in
                              quant qx uu____72714  in
                            (FStar_Parser_Const.op_Negation, uu____72695)  in
                          let uu____72733 =
                            let uu____72756 =
                              let uu____72777 =
                                let uu____72796 =
                                  let uu____72797 =
                                    let uu____72798 =
                                      let uu____72803 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____72804 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____72803, uu____72804)  in
                                    FStar_SMTEncoding_Util.mkLT uu____72798
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____72797
                                   in
                                quant xy uu____72796  in
                              (FStar_Parser_Const.op_LT, uu____72777)  in
                            let uu____72821 =
                              let uu____72844 =
                                let uu____72865 =
                                  let uu____72884 =
                                    let uu____72885 =
                                      let uu____72886 =
                                        let uu____72891 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____72892 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____72891, uu____72892)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____72886
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____72885
                                     in
                                  quant xy uu____72884  in
                                (FStar_Parser_Const.op_LTE, uu____72865)  in
                              let uu____72909 =
                                let uu____72932 =
                                  let uu____72953 =
                                    let uu____72972 =
                                      let uu____72973 =
                                        let uu____72974 =
                                          let uu____72979 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____72980 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____72979, uu____72980)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____72974
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____72973
                                       in
                                    quant xy uu____72972  in
                                  (FStar_Parser_Const.op_GT, uu____72953)  in
                                let uu____72997 =
                                  let uu____73020 =
                                    let uu____73041 =
                                      let uu____73060 =
                                        let uu____73061 =
                                          let uu____73062 =
                                            let uu____73067 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73068 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73067, uu____73068)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73062
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73061
                                         in
                                      quant xy uu____73060  in
                                    (FStar_Parser_Const.op_GTE, uu____73041)
                                     in
                                  let uu____73085 =
                                    let uu____73108 =
                                      let uu____73129 =
                                        let uu____73148 =
                                          let uu____73149 =
                                            let uu____73150 =
                                              let uu____73155 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____73156 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____73155, uu____73156)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____73150
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____73149
                                           in
                                        quant xy uu____73148  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____73129)
                                       in
                                    let uu____73173 =
                                      let uu____73196 =
                                        let uu____73217 =
                                          let uu____73236 =
                                            let uu____73237 =
                                              let uu____73238 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____73238
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____73237
                                             in
                                          quant qx uu____73236  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____73217)
                                         in
                                      let uu____73255 =
                                        let uu____73278 =
                                          let uu____73299 =
                                            let uu____73318 =
                                              let uu____73319 =
                                                let uu____73320 =
                                                  let uu____73325 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____73326 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____73325, uu____73326)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____73320
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____73319
                                               in
                                            quant xy uu____73318  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____73299)
                                           in
                                        let uu____73343 =
                                          let uu____73366 =
                                            let uu____73387 =
                                              let uu____73406 =
                                                let uu____73407 =
                                                  let uu____73408 =
                                                    let uu____73413 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____73414 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____73413,
                                                      uu____73414)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____73408
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____73407
                                                 in
                                              quant xy uu____73406  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____73387)
                                             in
                                          let uu____73431 =
                                            let uu____73454 =
                                              let uu____73475 =
                                                let uu____73494 =
                                                  let uu____73495 =
                                                    let uu____73496 =
                                                      let uu____73501 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____73502 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____73501,
                                                        uu____73502)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____73496
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____73495
                                                   in
                                                quant xy uu____73494  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____73475)
                                               in
                                            let uu____73519 =
                                              let uu____73542 =
                                                let uu____73563 =
                                                  let uu____73582 =
                                                    let uu____73583 =
                                                      let uu____73584 =
                                                        let uu____73589 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____73590 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____73589,
                                                          uu____73590)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____73584
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____73583
                                                     in
                                                  quant xy uu____73582  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____73563)
                                                 in
                                              let uu____73607 =
                                                let uu____73630 =
                                                  let uu____73651 =
                                                    let uu____73670 =
                                                      let uu____73671 =
                                                        let uu____73672 =
                                                          let uu____73677 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____73678 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____73677,
                                                            uu____73678)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____73672
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____73671
                                                       in
                                                    quant xy uu____73670  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____73651)
                                                   in
                                                let uu____73695 =
                                                  let uu____73718 =
                                                    let uu____73739 =
                                                      let uu____73758 =
                                                        let uu____73759 =
                                                          let uu____73760 =
                                                            let uu____73765 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____73766 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____73765,
                                                              uu____73766)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____73760
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____73759
                                                         in
                                                      quant xy uu____73758
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____73739)
                                                     in
                                                  let uu____73783 =
                                                    let uu____73806 =
                                                      let uu____73827 =
                                                        let uu____73846 =
                                                          let uu____73847 =
                                                            let uu____73848 =
                                                              let uu____73853
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____73854
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____73853,
                                                                uu____73854)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____73848
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____73847
                                                           in
                                                        quant xy uu____73846
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____73827)
                                                       in
                                                    let uu____73871 =
                                                      let uu____73894 =
                                                        let uu____73915 =
                                                          let uu____73934 =
                                                            let uu____73935 =
                                                              let uu____73936
                                                                =
                                                                let uu____73941
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____73942
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____73941,
                                                                  uu____73942)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____73936
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____73935
                                                             in
                                                          quant xy
                                                            uu____73934
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____73915)
                                                         in
                                                      let uu____73959 =
                                                        let uu____73982 =
                                                          let uu____74003 =
                                                            let uu____74022 =
                                                              let uu____74023
                                                                =
                                                                let uu____74024
                                                                  =
                                                                  let uu____74029
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74030
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74029,
                                                                    uu____74030)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74024
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74023
                                                               in
                                                            quant xy
                                                              uu____74022
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74003)
                                                           in
                                                        let uu____74047 =
                                                          let uu____74070 =
                                                            let uu____74091 =
                                                              let uu____74110
                                                                =
                                                                let uu____74111
                                                                  =
                                                                  let uu____74112
                                                                    =
                                                                    let uu____74117
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74118
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74117,
                                                                    uu____74118)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____74112
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____74111
                                                                 in
                                                              quant xy
                                                                uu____74110
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74091)
                                                             in
                                                          let uu____74135 =
                                                            let uu____74158 =
                                                              let uu____74179
                                                                =
                                                                let uu____74198
                                                                  =
                                                                  let uu____74199
                                                                    =
                                                                    let uu____74200
                                                                    =
                                                                    let uu____74205
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74206
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74205,
                                                                    uu____74206)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____74200
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____74199
                                                                   in
                                                                quant xy
                                                                  uu____74198
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____74179)
                                                               in
                                                            let uu____74223 =
                                                              let uu____74246
                                                                =
                                                                let uu____74267
                                                                  =
                                                                  let uu____74286
                                                                    =
                                                                    let uu____74287
                                                                    =
                                                                    let uu____74288
                                                                    =
                                                                    let uu____74293
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74294
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74293,
                                                                    uu____74294)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____74288
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____74287
                                                                     in
                                                                  quant xy
                                                                    uu____74286
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____74267)
                                                                 in
                                                              let uu____74311
                                                                =
                                                                let uu____74334
                                                                  =
                                                                  let uu____74355
                                                                    =
                                                                    let uu____74374
                                                                    =
                                                                    let uu____74375
                                                                    =
                                                                    let uu____74376
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____74376
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____74375
                                                                     in
                                                                    quant qx
                                                                    uu____74374
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____74355)
                                                                   in
                                                                [uu____74334]
                                                                 in
                                                              uu____74246 ::
                                                                uu____74311
                                                               in
                                                            uu____74158 ::
                                                              uu____74223
                                                             in
                                                          uu____74070 ::
                                                            uu____74135
                                                           in
                                                        uu____73982 ::
                                                          uu____74047
                                                         in
                                                      uu____73894 ::
                                                        uu____73959
                                                       in
                                                    uu____73806 ::
                                                      uu____73871
                                                     in
                                                  uu____73718 :: uu____73783
                                                   in
                                                uu____73630 :: uu____73695
                                                 in
                                              uu____73542 :: uu____73607  in
                                            uu____73454 :: uu____73519  in
                                          uu____73366 :: uu____73431  in
                                        uu____73278 :: uu____73343  in
                                      uu____73196 :: uu____73255  in
                                    uu____73108 :: uu____73173  in
                                  uu____73020 :: uu____73085  in
                                uu____72932 :: uu____72997  in
                              uu____72844 :: uu____72909  in
                            uu____72756 :: uu____72821  in
                          uu____72674 :: uu____72733  in
                        uu____72586 :: uu____72651  in
                      uu____72498 :: uu____72563  in
                    uu____72416 :: uu____72475  in
                  uu____72335 :: uu____72393  in
                let mk1 l v1 =
                  let uu____74915 =
                    let uu____74927 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75017  ->
                              match uu____75017 with
                              | (l',uu____75038) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____74927
                      (FStar_Option.map
                         (fun uu____75137  ->
                            match uu____75137 with
                            | (uu____75165,b) ->
                                let uu____75199 = FStar_Ident.range_of_lid l
                                   in
                                b uu____75199 v1))
                     in
                  FStar_All.pipe_right uu____74915 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____75282  ->
                          match uu____75282 with
                          | (l',uu____75303) -> FStar_Ident.lid_equals l l'))
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
          let uu____75377 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____75377 with
          | (xxsym,xx) ->
              let uu____75388 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____75388 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____75404 =
                     let uu____75412 =
                       let uu____75413 =
                         let uu____75424 =
                           let uu____75425 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____75435 =
                             let uu____75446 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____75446 :: vars  in
                           uu____75425 :: uu____75435  in
                         let uu____75472 =
                           let uu____75473 =
                             let uu____75478 =
                               let uu____75479 =
                                 let uu____75484 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____75484)  in
                               FStar_SMTEncoding_Util.mkEq uu____75479  in
                             (xx_has_type, uu____75478)  in
                           FStar_SMTEncoding_Util.mkImp uu____75473  in
                         ([[xx_has_type]], uu____75424, uu____75472)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____75413  in
                     let uu____75497 =
                       let uu____75499 =
                         let uu____75501 =
                           let uu____75503 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____75503  in
                         Prims.op_Hat module_name uu____75501  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____75499
                        in
                     (uu____75412,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____75497)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____75404)
  
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
    let uu____75559 =
      let uu____75561 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____75561  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____75559  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____75583 =
      let uu____75584 =
        let uu____75592 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____75592, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____75584  in
    let uu____75597 =
      let uu____75600 =
        let uu____75601 =
          let uu____75609 =
            let uu____75610 =
              let uu____75621 =
                let uu____75622 =
                  let uu____75627 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____75627)  in
                FStar_SMTEncoding_Util.mkImp uu____75622  in
              ([[typing_pred]], [xx], uu____75621)  in
            let uu____75652 =
              let uu____75667 = FStar_TypeChecker_Env.get_range env  in
              let uu____75668 = mkForall_fuel1 env  in
              uu____75668 uu____75667  in
            uu____75652 uu____75610  in
          (uu____75609, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____75601  in
      [uu____75600]  in
    uu____75583 :: uu____75597  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____75715 =
      let uu____75716 =
        let uu____75724 =
          let uu____75725 = FStar_TypeChecker_Env.get_range env  in
          let uu____75726 =
            let uu____75737 =
              let uu____75742 =
                let uu____75745 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____75745]  in
              [uu____75742]  in
            let uu____75750 =
              let uu____75751 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____75751 tt  in
            (uu____75737, [bb], uu____75750)  in
          FStar_SMTEncoding_Term.mkForall uu____75725 uu____75726  in
        (uu____75724, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____75716  in
    let uu____75776 =
      let uu____75779 =
        let uu____75780 =
          let uu____75788 =
            let uu____75789 =
              let uu____75800 =
                let uu____75801 =
                  let uu____75806 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____75806)  in
                FStar_SMTEncoding_Util.mkImp uu____75801  in
              ([[typing_pred]], [xx], uu____75800)  in
            let uu____75833 =
              let uu____75848 = FStar_TypeChecker_Env.get_range env  in
              let uu____75849 = mkForall_fuel1 env  in
              uu____75849 uu____75848  in
            uu____75833 uu____75789  in
          (uu____75788, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____75780  in
      [uu____75779]  in
    uu____75715 :: uu____75776  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____75892 =
        let uu____75893 =
          let uu____75899 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____75899, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____75893  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____75892  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____75913 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____75913  in
    let uu____75918 =
      let uu____75919 =
        let uu____75927 =
          let uu____75928 = FStar_TypeChecker_Env.get_range env  in
          let uu____75929 =
            let uu____75940 =
              let uu____75945 =
                let uu____75948 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____75948]  in
              [uu____75945]  in
            let uu____75953 =
              let uu____75954 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____75954 tt  in
            (uu____75940, [bb], uu____75953)  in
          FStar_SMTEncoding_Term.mkForall uu____75928 uu____75929  in
        (uu____75927, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____75919  in
    let uu____75979 =
      let uu____75982 =
        let uu____75983 =
          let uu____75991 =
            let uu____75992 =
              let uu____76003 =
                let uu____76004 =
                  let uu____76009 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76009)  in
                FStar_SMTEncoding_Util.mkImp uu____76004  in
              ([[typing_pred]], [xx], uu____76003)  in
            let uu____76036 =
              let uu____76051 = FStar_TypeChecker_Env.get_range env  in
              let uu____76052 = mkForall_fuel1 env  in
              uu____76052 uu____76051  in
            uu____76036 uu____75992  in
          (uu____75991, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____75983  in
      let uu____76074 =
        let uu____76077 =
          let uu____76078 =
            let uu____76086 =
              let uu____76087 =
                let uu____76098 =
                  let uu____76099 =
                    let uu____76104 =
                      let uu____76105 =
                        let uu____76108 =
                          let uu____76111 =
                            let uu____76114 =
                              let uu____76115 =
                                let uu____76120 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____76121 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____76120, uu____76121)  in
                              FStar_SMTEncoding_Util.mkGT uu____76115  in
                            let uu____76123 =
                              let uu____76126 =
                                let uu____76127 =
                                  let uu____76132 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____76133 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____76132, uu____76133)  in
                                FStar_SMTEncoding_Util.mkGTE uu____76127  in
                              let uu____76135 =
                                let uu____76138 =
                                  let uu____76139 =
                                    let uu____76144 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____76145 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____76144, uu____76145)  in
                                  FStar_SMTEncoding_Util.mkLT uu____76139  in
                                [uu____76138]  in
                              uu____76126 :: uu____76135  in
                            uu____76114 :: uu____76123  in
                          typing_pred_y :: uu____76111  in
                        typing_pred :: uu____76108  in
                      FStar_SMTEncoding_Util.mk_and_l uu____76105  in
                    (uu____76104, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____76099  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____76098)
                 in
              let uu____76178 =
                let uu____76193 = FStar_TypeChecker_Env.get_range env  in
                let uu____76194 = mkForall_fuel1 env  in
                uu____76194 uu____76193  in
              uu____76178 uu____76087  in
            (uu____76086,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76078  in
        [uu____76077]  in
      uu____75982 :: uu____76074  in
    uu____75918 :: uu____75979  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____76237 =
        let uu____76238 =
          let uu____76244 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76244, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76238  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76237  in
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
      let uu____76260 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76260  in
    let uu____76265 =
      let uu____76266 =
        let uu____76274 =
          let uu____76275 = FStar_TypeChecker_Env.get_range env  in
          let uu____76276 =
            let uu____76287 =
              let uu____76292 =
                let uu____76295 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____76295]  in
              [uu____76292]  in
            let uu____76300 =
              let uu____76301 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76301 tt  in
            (uu____76287, [bb], uu____76300)  in
          FStar_SMTEncoding_Term.mkForall uu____76275 uu____76276  in
        (uu____76274, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76266  in
    let uu____76326 =
      let uu____76329 =
        let uu____76330 =
          let uu____76338 =
            let uu____76339 =
              let uu____76350 =
                let uu____76351 =
                  let uu____76356 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____76356)  in
                FStar_SMTEncoding_Util.mkImp uu____76351  in
              ([[typing_pred]], [xx], uu____76350)  in
            let uu____76383 =
              let uu____76398 = FStar_TypeChecker_Env.get_range env  in
              let uu____76399 = mkForall_fuel1 env  in
              uu____76399 uu____76398  in
            uu____76383 uu____76339  in
          (uu____76338, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76330  in
      let uu____76421 =
        let uu____76424 =
          let uu____76425 =
            let uu____76433 =
              let uu____76434 =
                let uu____76445 =
                  let uu____76446 =
                    let uu____76451 =
                      let uu____76452 =
                        let uu____76455 =
                          let uu____76458 =
                            let uu____76461 =
                              let uu____76462 =
                                let uu____76467 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____76468 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____76467, uu____76468)  in
                              FStar_SMTEncoding_Util.mkGT uu____76462  in
                            let uu____76470 =
                              let uu____76473 =
                                let uu____76474 =
                                  let uu____76479 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____76480 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____76479, uu____76480)  in
                                FStar_SMTEncoding_Util.mkGTE uu____76474  in
                              let uu____76482 =
                                let uu____76485 =
                                  let uu____76486 =
                                    let uu____76491 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____76492 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____76491, uu____76492)  in
                                  FStar_SMTEncoding_Util.mkLT uu____76486  in
                                [uu____76485]  in
                              uu____76473 :: uu____76482  in
                            uu____76461 :: uu____76470  in
                          typing_pred_y :: uu____76458  in
                        typing_pred :: uu____76455  in
                      FStar_SMTEncoding_Util.mk_and_l uu____76452  in
                    (uu____76451, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____76446  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____76445)
                 in
              let uu____76525 =
                let uu____76540 = FStar_TypeChecker_Env.get_range env  in
                let uu____76541 = mkForall_fuel1 env  in
                uu____76541 uu____76540  in
              uu____76525 uu____76434  in
            (uu____76433,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76425  in
        [uu____76424]  in
      uu____76329 :: uu____76421  in
    uu____76265 :: uu____76326  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76588 =
      let uu____76589 =
        let uu____76597 =
          let uu____76598 = FStar_TypeChecker_Env.get_range env  in
          let uu____76599 =
            let uu____76610 =
              let uu____76615 =
                let uu____76618 = FStar_SMTEncoding_Term.boxString b  in
                [uu____76618]  in
              [uu____76615]  in
            let uu____76623 =
              let uu____76624 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76624 tt  in
            (uu____76610, [bb], uu____76623)  in
          FStar_SMTEncoding_Term.mkForall uu____76598 uu____76599  in
        (uu____76597, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76589  in
    let uu____76649 =
      let uu____76652 =
        let uu____76653 =
          let uu____76661 =
            let uu____76662 =
              let uu____76673 =
                let uu____76674 =
                  let uu____76679 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____76679)  in
                FStar_SMTEncoding_Util.mkImp uu____76674  in
              ([[typing_pred]], [xx], uu____76673)  in
            let uu____76706 =
              let uu____76721 = FStar_TypeChecker_Env.get_range env  in
              let uu____76722 = mkForall_fuel1 env  in
              uu____76722 uu____76721  in
            uu____76706 uu____76662  in
          (uu____76661, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76653  in
      [uu____76652]  in
    uu____76588 :: uu____76649  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____76769 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____76769]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____76799 =
      let uu____76800 =
        let uu____76808 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____76808, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76800  in
    [uu____76799]  in
  let mk_and_interp env conj uu____76831 =
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
    let uu____76860 =
      let uu____76861 =
        let uu____76869 =
          let uu____76870 = FStar_TypeChecker_Env.get_range env  in
          let uu____76871 =
            let uu____76882 =
              let uu____76883 =
                let uu____76888 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____76888, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____76883  in
            ([[l_and_a_b]], [aa; bb], uu____76882)  in
          FStar_SMTEncoding_Term.mkForall uu____76870 uu____76871  in
        (uu____76869, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76861  in
    [uu____76860]  in
  let mk_or_interp env disj uu____76943 =
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
    let uu____76972 =
      let uu____76973 =
        let uu____76981 =
          let uu____76982 = FStar_TypeChecker_Env.get_range env  in
          let uu____76983 =
            let uu____76994 =
              let uu____76995 =
                let uu____77000 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77000, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____76995  in
            ([[l_or_a_b]], [aa; bb], uu____76994)  in
          FStar_SMTEncoding_Term.mkForall uu____76982 uu____76983  in
        (uu____76981, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76973  in
    [uu____76972]  in
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
    let uu____77078 =
      let uu____77079 =
        let uu____77087 =
          let uu____77088 = FStar_TypeChecker_Env.get_range env  in
          let uu____77089 =
            let uu____77100 =
              let uu____77101 =
                let uu____77106 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____77106, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77101  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____77100)  in
          FStar_SMTEncoding_Term.mkForall uu____77088 uu____77089  in
        (uu____77087, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77079  in
    [uu____77078]  in
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
    let uu____77196 =
      let uu____77197 =
        let uu____77205 =
          let uu____77206 = FStar_TypeChecker_Env.get_range env  in
          let uu____77207 =
            let uu____77218 =
              let uu____77219 =
                let uu____77224 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____77224, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77219  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____77218)  in
          FStar_SMTEncoding_Term.mkForall uu____77206 uu____77207  in
        (uu____77205, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77197  in
    [uu____77196]  in
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
    let uu____77324 =
      let uu____77325 =
        let uu____77333 =
          let uu____77334 = FStar_TypeChecker_Env.get_range env  in
          let uu____77335 =
            let uu____77346 =
              let uu____77347 =
                let uu____77352 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____77352, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77347  in
            ([[l_imp_a_b]], [aa; bb], uu____77346)  in
          FStar_SMTEncoding_Term.mkForall uu____77334 uu____77335  in
        (uu____77333, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77325  in
    [uu____77324]  in
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
    let uu____77436 =
      let uu____77437 =
        let uu____77445 =
          let uu____77446 = FStar_TypeChecker_Env.get_range env  in
          let uu____77447 =
            let uu____77458 =
              let uu____77459 =
                let uu____77464 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____77464, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77459  in
            ([[l_iff_a_b]], [aa; bb], uu____77458)  in
          FStar_SMTEncoding_Term.mkForall uu____77446 uu____77447  in
        (uu____77445, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77437  in
    [uu____77436]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____77535 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____77535  in
    let uu____77540 =
      let uu____77541 =
        let uu____77549 =
          let uu____77550 = FStar_TypeChecker_Env.get_range env  in
          let uu____77551 =
            let uu____77562 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____77562)  in
          FStar_SMTEncoding_Term.mkForall uu____77550 uu____77551  in
        (uu____77549, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77541  in
    [uu____77540]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____77615 =
      let uu____77616 =
        let uu____77624 =
          let uu____77625 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____77625 range_ty  in
        let uu____77626 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____77624, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____77626)
         in
      FStar_SMTEncoding_Util.mkAssume uu____77616  in
    [uu____77615]  in
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
        let uu____77672 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____77672 x1 t  in
      let uu____77674 = FStar_TypeChecker_Env.get_range env  in
      let uu____77675 =
        let uu____77686 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____77686)  in
      FStar_SMTEncoding_Term.mkForall uu____77674 uu____77675  in
    let uu____77711 =
      let uu____77712 =
        let uu____77720 =
          let uu____77721 = FStar_TypeChecker_Env.get_range env  in
          let uu____77722 =
            let uu____77733 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____77733)  in
          FStar_SMTEncoding_Term.mkForall uu____77721 uu____77722  in
        (uu____77720,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77712  in
    [uu____77711]  in
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
    let uu____77794 =
      let uu____77795 =
        let uu____77803 =
          let uu____77804 = FStar_TypeChecker_Env.get_range env  in
          let uu____77805 =
            let uu____77821 =
              let uu____77822 =
                let uu____77827 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____77828 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____77827, uu____77828)  in
              FStar_SMTEncoding_Util.mkAnd uu____77822  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____77821)
             in
          FStar_SMTEncoding_Term.mkForall' uu____77804 uu____77805  in
        (uu____77803,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77795  in
    [uu____77794]  in
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
          let uu____78386 =
            FStar_Util.find_opt
              (fun uu____78424  ->
                 match uu____78424 with
                 | (l,uu____78440) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____78386 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____78483,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____78544 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____78544 with
        | (form,decls) ->
            let uu____78553 =
              let uu____78556 =
                let uu____78559 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____78559]  in
              FStar_All.pipe_right uu____78556
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____78553
  
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
              let uu____78618 =
                ((let uu____78622 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____78622) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____78618
              then
                let arg_sorts =
                  let uu____78634 =
                    let uu____78635 = FStar_Syntax_Subst.compress t_norm  in
                    uu____78635.FStar_Syntax_Syntax.n  in
                  match uu____78634 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____78641) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____78679  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____78686 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____78688 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____78688 with
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
                    let uu____78724 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____78724, env1)
              else
                (let uu____78729 = prims.is lid  in
                 if uu____78729
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____78738 = prims.mk lid vname  in
                   match uu____78738 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____78762 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____78762, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____78771 =
                      let uu____78790 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____78790 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____78818 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____78818
                            then
                              let uu____78823 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_78826 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_78826.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_78826.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_78826.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_78826.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_78826.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_78826.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_78826.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_78826.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_78826.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_78826.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_78826.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_78826.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_78826.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_78826.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_78826.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_78826.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_78826.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_78826.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_78826.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_78826.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_78826.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_78826.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_78826.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_78826.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_78826.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_78826.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_78826.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_78826.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_78826.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_78826.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_78826.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_78826.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_78826.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_78826.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_78826.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_78826.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_78826.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_78826.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_78826.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_78826.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_78826.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_78826.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____78823
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____78849 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____78849)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____78771 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_78955  ->
                                  match uu___639_78955 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____78959 =
                                        FStar_Util.prefix vars  in
                                      (match uu____78959 with
                                       | (uu____78992,xxv) ->
                                           let xx =
                                             let uu____79031 =
                                               let uu____79032 =
                                                 let uu____79038 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79038,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79032
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79031
                                              in
                                           let uu____79041 =
                                             let uu____79042 =
                                               let uu____79050 =
                                                 let uu____79051 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79052 =
                                                   let uu____79063 =
                                                     let uu____79064 =
                                                       let uu____79069 =
                                                         let uu____79070 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79070
                                                          in
                                                       (vapp, uu____79069)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79064
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79063)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79051 uu____79052
                                                  in
                                               (uu____79050,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79042
                                              in
                                           [uu____79041])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79085 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79085 with
                                       | (uu____79118,xxv) ->
                                           let xx =
                                             let uu____79157 =
                                               let uu____79158 =
                                                 let uu____79164 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79164,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79158
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79157
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
                                           let uu____79175 =
                                             let uu____79176 =
                                               let uu____79184 =
                                                 let uu____79185 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79186 =
                                                   let uu____79197 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79197)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79185 uu____79186
                                                  in
                                               (uu____79184,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79176
                                              in
                                           [uu____79175])
                                  | uu____79210 -> []))
                           in
                        let uu____79211 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____79211 with
                         | (vars,guards,env',decls1,uu____79236) ->
                             let uu____79249 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____79262 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____79262, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____79266 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____79266 with
                                    | (g,ds) ->
                                        let uu____79279 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____79279,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____79249 with
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
                                  let should_thunk uu____79302 =
                                    let is_type1 t =
                                      let uu____79310 =
                                        let uu____79311 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____79311.FStar_Syntax_Syntax.n  in
                                      match uu____79310 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____79315 -> true
                                      | uu____79317 -> false  in
                                    let is_squash1 t =
                                      let uu____79326 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____79326 with
                                      | (head1,uu____79345) ->
                                          let uu____79370 =
                                            let uu____79371 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____79371.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____79370 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____79376;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____79377;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____79379;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____79380;_};_},uu____79381)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____79389 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____79394 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____79394))
                                       &&
                                       (let uu____79400 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____79400))
                                      &&
                                      (let uu____79403 = is_type1 t_norm  in
                                       Prims.op_Negation uu____79403)
                                     in
                                  let uu____79405 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____79464 -> (false, vars)  in
                                  (match uu____79405 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____79514 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____79514 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____79550 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____79559 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____79559
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____79570 ->
                                                  let uu____79579 =
                                                    let uu____79587 =
                                                      get_vtok ()  in
                                                    (uu____79587, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____79579
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____79594 =
                                                let uu____79602 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____79602)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____79594
                                               in
                                            let uu____79616 =
                                              let vname_decl =
                                                let uu____79624 =
                                                  let uu____79636 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____79636,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____79624
                                                 in
                                              let uu____79647 =
                                                let env2 =
                                                  let uu___1026_79653 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_79653.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____79654 =
                                                  let uu____79656 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____79656
                                                   in
                                                if uu____79654
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____79647 with
                                              | (tok_typing,decls2) ->
                                                  let uu____79673 =
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
                                                        let uu____79699 =
                                                          let uu____79702 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____79702
                                                           in
                                                        let uu____79709 =
                                                          let uu____79710 =
                                                            let uu____79713 =
                                                              let uu____79714
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____79714
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _79718  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _79718)
                                                              uu____79713
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____79710
                                                           in
                                                        (uu____79699,
                                                          uu____79709)
                                                    | uu____79725 when
                                                        thunked ->
                                                        let uu____79736 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____79736
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____79751
                                                                 =
                                                                 let uu____79759
                                                                   =
                                                                   let uu____79762
                                                                    =
                                                                    let uu____79765
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____79765]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____79762
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____79759)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____79751
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____79773
                                                               =
                                                               let uu____79781
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____79781,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____79773
                                                              in
                                                           let uu____79786 =
                                                             let uu____79789
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____79789
                                                              in
                                                           (uu____79786,
                                                             env1))
                                                    | uu____79798 ->
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
                                                          let uu____79822 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____79823 =
                                                            let uu____79834 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____79834)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____79822
                                                            uu____79823
                                                           in
                                                        let name_tok_corr =
                                                          let uu____79844 =
                                                            let uu____79852 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____79852,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____79844
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
                                                            let uu____79863 =
                                                              let uu____79864
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____79864]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____79863
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____79891 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____79892 =
                                                              let uu____79903
                                                                =
                                                                let uu____79904
                                                                  =
                                                                  let uu____79909
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____79910
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____79909,
                                                                    uu____79910)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____79904
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____79903)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____79891
                                                              uu____79892
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____79939 =
                                                          let uu____79942 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____79942
                                                           in
                                                        (uu____79939, env1)
                                                     in
                                                  (match uu____79673 with
                                                   | (tok_decl,env2) ->
                                                       let uu____79963 =
                                                         let uu____79966 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____79966
                                                           tok_decl
                                                          in
                                                       (uu____79963, env2))
                                               in
                                            (match uu____79616 with
                                             | (decls2,env2) ->
                                                 let uu____79985 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____79995 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____79995 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80010 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80010, decls)
                                                    in
                                                 (match uu____79985 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80025 =
                                                          let uu____80033 =
                                                            let uu____80034 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80035 =
                                                              let uu____80046
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80046)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80034
                                                              uu____80035
                                                             in
                                                          (uu____80033,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80025
                                                         in
                                                      let freshness =
                                                        let uu____80062 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80062
                                                        then
                                                          let uu____80070 =
                                                            let uu____80071 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80072 =
                                                              let uu____80085
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____80092
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80085,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____80092)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80071
                                                              uu____80072
                                                             in
                                                          let uu____80098 =
                                                            let uu____80101 =
                                                              let uu____80102
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____80102
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____80101]  in
                                                          uu____80070 ::
                                                            uu____80098
                                                        else []  in
                                                      let g =
                                                        let uu____80108 =
                                                          let uu____80111 =
                                                            let uu____80114 =
                                                              let uu____80117
                                                                =
                                                                let uu____80120
                                                                  =
                                                                  let uu____80123
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____80123
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____80120
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____80117
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____80114
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80111
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____80108
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
          let uu____80163 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____80163 with
          | FStar_Pervasives_Native.None  ->
              let uu____80174 = encode_free_var false env x t t_norm []  in
              (match uu____80174 with
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
            let uu____80237 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____80237 with
            | (decls,env1) ->
                let uu____80248 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____80248
                then
                  let uu____80255 =
                    let uu____80256 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____80256  in
                  (uu____80255, env1)
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
             (fun uu____80312  ->
                fun lb  ->
                  match uu____80312 with
                  | (decls,env1) ->
                      let uu____80332 =
                        let uu____80337 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____80337
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____80332 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____80366 = FStar_Syntax_Util.head_and_args t  in
    match uu____80366 with
    | (hd1,args) ->
        let uu____80410 =
          let uu____80411 = FStar_Syntax_Util.un_uinst hd1  in
          uu____80411.FStar_Syntax_Syntax.n  in
        (match uu____80410 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____80417,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____80441 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____80452 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_80460 = en  in
    let uu____80461 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_80460.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_80460.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_80460.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_80460.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_80460.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_80460.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_80460.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_80460.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_80460.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_80460.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____80461
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____80491  ->
      fun quals  ->
        match uu____80491 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____80596 = FStar_Util.first_N nbinders formals  in
              match uu____80596 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____80697  ->
                         fun uu____80698  ->
                           match (uu____80697, uu____80698) with
                           | ((formal,uu____80724),(binder,uu____80726)) ->
                               let uu____80747 =
                                 let uu____80754 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____80754)  in
                               FStar_Syntax_Syntax.NT uu____80747) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____80768 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____80809  ->
                              match uu____80809 with
                              | (x,i) ->
                                  let uu____80828 =
                                    let uu___1139_80829 = x  in
                                    let uu____80830 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_80829.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_80829.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____80830
                                    }  in
                                  (uu____80828, i)))
                       in
                    FStar_All.pipe_right uu____80768
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____80854 =
                      let uu____80859 = FStar_Syntax_Subst.compress body  in
                      let uu____80860 =
                        let uu____80861 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____80861
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____80859
                        uu____80860
                       in
                    uu____80854 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_80912 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_80912.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_80912.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_80912.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_80912.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_80912.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_80912.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_80912.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_80912.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_80912.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_80912.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_80912.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_80912.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_80912.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_80912.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_80912.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_80912.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_80912.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_80912.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_80912.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_80912.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_80912.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_80912.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_80912.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_80912.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_80912.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_80912.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_80912.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_80912.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_80912.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_80912.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_80912.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_80912.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_80912.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_80912.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_80912.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_80912.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_80912.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_80912.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_80912.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_80912.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_80912.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_80912.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____80984  ->
                       fun uu____80985  ->
                         match (uu____80984, uu____80985) with
                         | ((x,uu____81011),(b,uu____81013)) ->
                             let uu____81034 =
                               let uu____81041 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81041)  in
                             FStar_Syntax_Syntax.NT uu____81034) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81066 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81066
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____81095 ->
                    let uu____81102 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____81102
                | uu____81103 when Prims.op_Negation norm1 ->
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
                | uu____81106 ->
                    let uu____81107 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____81107)
                 in
              let aux t1 e1 =
                let uu____81149 = FStar_Syntax_Util.abs_formals e1  in
                match uu____81149 with
                | (binders,body,lopt) ->
                    let uu____81181 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____81197 -> arrow_formals_comp_norm false t1  in
                    (match uu____81181 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____81231 =
                           if nformals < nbinders
                           then
                             let uu____81275 =
                               FStar_Util.first_N nformals binders  in
                             match uu____81275 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____81359 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____81359)
                           else
                             if nformals > nbinders
                             then
                               (let uu____81399 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____81399 with
                                | (binders1,body1) ->
                                    let uu____81452 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____81452))
                             else
                               (let uu____81465 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____81465))
                            in
                         (match uu____81231 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____81525 = aux t e  in
              match uu____81525 with
              | (binders,body,comp) ->
                  let uu____81571 =
                    let uu____81582 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____81582
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____81597 = aux comp1 body1  in
                      match uu____81597 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____81571 with
                   | (binders1,body1,comp1) ->
                       let uu____81680 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____81680, comp1))
               in
            (try
               (fun uu___1216_81707  ->
                  match () with
                  | () ->
                      let uu____81714 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____81714
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____81730 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____81793  ->
                                   fun lb  ->
                                     match uu____81793 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____81848 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____81848
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____81854 =
                                             let uu____81863 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____81863
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____81854 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____81730 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82004;
                                    FStar_Syntax_Syntax.lbeff = uu____82005;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82007;
                                    FStar_Syntax_Syntax.lbpos = uu____82008;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82032 =
                                     let uu____82039 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82039 with
                                     | (tcenv',uu____82055,e_t) ->
                                         let uu____82061 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82072 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82061 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82089 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82089.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82032 with
                                    | (env',e1,t_norm1) ->
                                        let uu____82099 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____82099 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____82119 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____82119
                                               then
                                                 let uu____82124 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____82127 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____82124 uu____82127
                                               else ());
                                              (let uu____82132 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____82132 with
                                               | (vars,_guards,env'1,binder_decls,uu____82159)
                                                   ->
                                                   let uu____82172 =
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
                                                         let uu____82189 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____82189
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____82211 =
                                                          let uu____82212 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____82213 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____82212 fvb
                                                            uu____82213
                                                           in
                                                        (vars, uu____82211))
                                                      in
                                                   (match uu____82172 with
                                                    | (vars1,app) ->
                                                        let uu____82224 =
                                                          let is_logical =
                                                            let uu____82237 =
                                                              let uu____82238
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____82238.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____82237
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____82244 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____82248 =
                                                              let uu____82249
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____82249
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____82248
                                                              (fun lid  ->
                                                                 let uu____82258
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____82258
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____82259 =
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
                                                          if uu____82259
                                                          then
                                                            let uu____82275 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____82276 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____82275,
                                                              uu____82276)
                                                          else
                                                            (let uu____82287
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____82287))
                                                           in
                                                        (match uu____82224
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____82311
                                                                 =
                                                                 let uu____82319
                                                                   =
                                                                   let uu____82320
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____82321
                                                                    =
                                                                    let uu____82332
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____82332)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____82320
                                                                    uu____82321
                                                                    in
                                                                 let uu____82341
                                                                   =
                                                                   let uu____82342
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____82342
                                                                    in
                                                                 (uu____82319,
                                                                   uu____82341,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____82311
                                                                in
                                                             let uu____82348
                                                               =
                                                               let uu____82351
                                                                 =
                                                                 let uu____82354
                                                                   =
                                                                   let uu____82357
                                                                    =
                                                                    let uu____82360
                                                                    =
                                                                    let uu____82363
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____82363
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____82360
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____82357
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____82354
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____82351
                                                                in
                                                             (uu____82348,
                                                               env2)))))))
                               | uu____82372 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____82432 =
                                   let uu____82438 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____82438,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____82432  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____82444 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____82497  ->
                                         fun fvb  ->
                                           match uu____82497 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____82552 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____82552
                                                  in
                                               let gtok =
                                                 let uu____82556 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____82556
                                                  in
                                               let env4 =
                                                 let uu____82559 =
                                                   let uu____82562 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _82568  ->
                                                        FStar_Pervasives_Native.Some
                                                          _82568) uu____82562
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____82559
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____82444 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____82688
                                     t_norm uu____82690 =
                                     match (uu____82688, uu____82690) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____82720;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____82721;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____82723;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____82724;_})
                                         ->
                                         let uu____82751 =
                                           let uu____82758 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____82758 with
                                           | (tcenv',uu____82774,e_t) ->
                                               let uu____82780 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____82791 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____82780 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_82808 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_82808.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____82751 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____82821 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____82821
                                                then
                                                  let uu____82826 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____82828 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____82830 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____82826 uu____82828
                                                    uu____82830
                                                else ());
                                               (let uu____82835 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____82835 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____82862 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____82862 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____82884 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____82884
                                                           then
                                                             let uu____82889
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____82891
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____82894
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____82896
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____82889
                                                               uu____82891
                                                               uu____82894
                                                               uu____82896
                                                           else ());
                                                          (let uu____82901 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____82901
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____82930)
                                                               ->
                                                               let uu____82943
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____82956
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____82956,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____82960
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____82960
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____82973
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____82973,
                                                                    decls0))
                                                                  in
                                                               (match uu____82943
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
                                                                    let uu____82994
                                                                    =
                                                                    let uu____83006
                                                                    =
                                                                    let uu____83009
                                                                    =
                                                                    let uu____83012
                                                                    =
                                                                    let uu____83015
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83015
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83012
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83009
                                                                     in
                                                                    (g,
                                                                    uu____83006,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____82994
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
                                                                    let uu____83045
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83045
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
                                                                    let uu____83060
                                                                    =
                                                                    let uu____83063
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83063
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83060
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83069
                                                                    =
                                                                    let uu____83072
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83072
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83069
                                                                     in
                                                                    let uu____83077
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83077
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____83093
                                                                    =
                                                                    let uu____83101
                                                                    =
                                                                    let uu____83102
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83103
                                                                    =
                                                                    let uu____83119
                                                                    =
                                                                    let uu____83120
                                                                    =
                                                                    let uu____83125
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____83125)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83120
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83119)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____83102
                                                                    uu____83103
                                                                     in
                                                                    let uu____83139
                                                                    =
                                                                    let uu____83140
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____83140
                                                                     in
                                                                    (uu____83101,
                                                                    uu____83139,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83093
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____83147
                                                                    =
                                                                    let uu____83155
                                                                    =
                                                                    let uu____83156
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83157
                                                                    =
                                                                    let uu____83168
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____83168)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83156
                                                                    uu____83157
                                                                     in
                                                                    (uu____83155,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83147
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____83182
                                                                    =
                                                                    let uu____83190
                                                                    =
                                                                    let uu____83191
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83192
                                                                    =
                                                                    let uu____83203
                                                                    =
                                                                    let uu____83204
                                                                    =
                                                                    let uu____83209
                                                                    =
                                                                    let uu____83210
                                                                    =
                                                                    let uu____83213
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____83213
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83210
                                                                     in
                                                                    (gsapp,
                                                                    uu____83209)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____83204
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83203)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83191
                                                                    uu____83192
                                                                     in
                                                                    (uu____83190,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83182
                                                                     in
                                                                    let uu____83227
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
                                                                    let uu____83239
                                                                    =
                                                                    let uu____83240
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83240
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____83239
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____83242
                                                                    =
                                                                    let uu____83250
                                                                    =
                                                                    let uu____83251
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83252
                                                                    =
                                                                    let uu____83263
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83263)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83251
                                                                    uu____83252
                                                                     in
                                                                    (uu____83250,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83242
                                                                     in
                                                                    let uu____83276
                                                                    =
                                                                    let uu____83285
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____83285
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____83300
                                                                    =
                                                                    let uu____83303
                                                                    =
                                                                    let uu____83304
                                                                    =
                                                                    let uu____83312
                                                                    =
                                                                    let uu____83313
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83314
                                                                    =
                                                                    let uu____83325
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83325)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83313
                                                                    uu____83314
                                                                     in
                                                                    (uu____83312,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83304
                                                                     in
                                                                    [uu____83303]
                                                                     in
                                                                    (d3,
                                                                    uu____83300)
                                                                     in
                                                                    match uu____83276
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____83227
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____83382
                                                                    =
                                                                    let uu____83385
                                                                    =
                                                                    let uu____83388
                                                                    =
                                                                    let uu____83391
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____83391
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____83388
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____83385
                                                                     in
                                                                    let uu____83398
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____83382,
                                                                    uu____83398,
                                                                    env02))))))))))
                                      in
                                   let uu____83403 =
                                     let uu____83416 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____83479  ->
                                          fun uu____83480  ->
                                            match (uu____83479, uu____83480)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____83605 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____83605 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____83416
                                      in
                                   (match uu____83403 with
                                    | (decls2,eqns,env01) ->
                                        let uu____83672 =
                                          let isDeclFun uu___640_83689 =
                                            match uu___640_83689 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____83691 -> true
                                            | uu____83704 -> false  in
                                          let uu____83706 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____83706
                                            (fun decls3  ->
                                               let uu____83736 =
                                                 FStar_List.fold_left
                                                   (fun uu____83767  ->
                                                      fun elt  ->
                                                        match uu____83767
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____83808 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____83808
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____83836
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____83836
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
                                                                    let uu___1459_83874
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_83874.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_83874.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_83874.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____83736 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____83906 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____83906, elts, rest))
                                           in
                                        (match uu____83672 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____83935 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_83941  ->
                                        match uu___641_83941 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____83944 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____83952 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____83952)))
                                in
                             if uu____83935
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_83974  ->
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
                   let uu____84013 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84013
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84032 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84032, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84088 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84088 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____84094 = encode_sigelt' env se  in
      match uu____84094 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____84106 =
                  let uu____84109 =
                    let uu____84110 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____84110  in
                  [uu____84109]  in
                FStar_All.pipe_right uu____84106
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____84115 ->
                let uu____84116 =
                  let uu____84119 =
                    let uu____84122 =
                      let uu____84123 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____84123  in
                    [uu____84122]  in
                  FStar_All.pipe_right uu____84119
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____84130 =
                  let uu____84133 =
                    let uu____84136 =
                      let uu____84139 =
                        let uu____84140 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____84140  in
                      [uu____84139]  in
                    FStar_All.pipe_right uu____84136
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____84133  in
                FStar_List.append uu____84116 uu____84130
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____84154 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____84154
       then
         let uu____84159 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____84159
       else ());
      (let is_opaque_to_smt t =
         let uu____84171 =
           let uu____84172 = FStar_Syntax_Subst.compress t  in
           uu____84172.FStar_Syntax_Syntax.n  in
         match uu____84171 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____84177)) -> s = "opaque_to_smt"
         | uu____84182 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____84191 =
           let uu____84192 = FStar_Syntax_Subst.compress t  in
           uu____84192.FStar_Syntax_Syntax.n  in
         match uu____84191 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____84197)) -> s = "uninterpreted_by_smt"
         | uu____84202 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____84208 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____84214 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____84226 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____84227 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____84228 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____84241 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____84243 =
             let uu____84245 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____84245  in
           if uu____84243
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____84274 ->
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
                let uu____84306 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____84306 with
                | (formals,uu____84326) ->
                    let arity = FStar_List.length formals  in
                    let uu____84350 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____84350 with
                     | (aname,atok,env2) ->
                         let uu____84376 =
                           let uu____84381 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____84381 env2
                            in
                         (match uu____84376 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____84393 =
                                  let uu____84394 =
                                    let uu____84406 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____84426  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____84406,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____84394
                                   in
                                [uu____84393;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____84443 =
                                let aux uu____84489 uu____84490 =
                                  match (uu____84489, uu____84490) with
                                  | ((bv,uu____84534),(env3,acc_sorts,acc))
                                      ->
                                      let uu____84566 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____84566 with
                                       | (xxsym,xx,env4) ->
                                           let uu____84589 =
                                             let uu____84592 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____84592 :: acc_sorts  in
                                           (env4, uu____84589, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____84443 with
                               | (uu____84624,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____84640 =
                                       let uu____84648 =
                                         let uu____84649 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____84650 =
                                           let uu____84661 =
                                             let uu____84662 =
                                               let uu____84667 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____84667)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____84662
                                              in
                                           ([[app]], xs_sorts, uu____84661)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____84649 uu____84650
                                          in
                                       (uu____84648,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____84640
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____84682 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____84682
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____84685 =
                                       let uu____84693 =
                                         let uu____84694 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____84695 =
                                           let uu____84706 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____84706)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____84694 uu____84695
                                          in
                                       (uu____84693,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____84685
                                      in
                                   let uu____84719 =
                                     let uu____84722 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____84722  in
                                   (env2, uu____84719))))
                 in
              let uu____84731 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____84731 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____84757,uu____84758)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____84759 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____84759 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____84781,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____84788 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_84794  ->
                       match uu___642_84794 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____84797 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____84803 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____84806 -> false))
                in
             Prims.op_Negation uu____84788  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____84816 =
                let uu____84821 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____84821 env fv t quals  in
              match uu____84816 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____84835 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____84835  in
                  let uu____84838 =
                    let uu____84839 =
                      let uu____84842 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____84842
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____84839  in
                  (uu____84838, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____84852 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____84852 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_84864 = env  in
                  let uu____84865 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_84864.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_84864.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_84864.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____84865;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_84864.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_84864.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_84864.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_84864.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_84864.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_84864.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_84864.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____84867 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____84867 with
                 | (f3,decls) ->
                     let g =
                       let uu____84881 =
                         let uu____84884 =
                           let uu____84885 =
                             let uu____84893 =
                               let uu____84894 =
                                 let uu____84896 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____84896
                                  in
                               FStar_Pervasives_Native.Some uu____84894  in
                             let uu____84900 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____84893, uu____84900)  in
                           FStar_SMTEncoding_Util.mkAssume uu____84885  in
                         [uu____84884]  in
                       FStar_All.pipe_right uu____84881
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____84909) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____84923 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____84945 =
                        let uu____84948 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____84948.FStar_Syntax_Syntax.fv_name  in
                      uu____84945.FStar_Syntax_Syntax.v  in
                    let uu____84949 =
                      let uu____84951 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____84951  in
                    if uu____84949
                    then
                      let val_decl =
                        let uu___1629_84983 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_84983.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_84983.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_84983.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____84984 = encode_sigelt' env1 val_decl  in
                      match uu____84984 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____84923 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85020,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85022;
                           FStar_Syntax_Syntax.lbtyp = uu____85023;
                           FStar_Syntax_Syntax.lbeff = uu____85024;
                           FStar_Syntax_Syntax.lbdef = uu____85025;
                           FStar_Syntax_Syntax.lbattrs = uu____85026;
                           FStar_Syntax_Syntax.lbpos = uu____85027;_}::[]),uu____85028)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85047 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85047 with
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
                  let uu____85085 =
                    let uu____85088 =
                      let uu____85089 =
                        let uu____85097 =
                          let uu____85098 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____85099 =
                            let uu____85110 =
                              let uu____85111 =
                                let uu____85116 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____85116)  in
                              FStar_SMTEncoding_Util.mkEq uu____85111  in
                            ([[b2t_x]], [xx], uu____85110)  in
                          FStar_SMTEncoding_Term.mkForall uu____85098
                            uu____85099
                           in
                        (uu____85097,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85089  in
                    [uu____85088]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85085
                   in
                let uu____85154 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____85154, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____85157,uu____85158) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_85168  ->
                   match uu___643_85168 with
                   | FStar_Syntax_Syntax.Discriminator uu____85170 -> true
                   | uu____85172 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____85174,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____85186 =
                      let uu____85188 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____85188.FStar_Ident.idText  in
                    uu____85186 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_85195  ->
                      match uu___644_85195 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____85198 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____85201) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_85215  ->
                   match uu___645_85215 with
                   | FStar_Syntax_Syntax.Projector uu____85217 -> true
                   | uu____85223 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____85227 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____85227 with
            | FStar_Pervasives_Native.Some uu____85234 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_85236 = se  in
                  let uu____85237 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____85237;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_85236.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_85236.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_85236.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____85240) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____85255) ->
           let uu____85264 = encode_sigelts env ses  in
           (match uu____85264 with
            | (g,env1) ->
                let uu____85275 =
                  FStar_List.fold_left
                    (fun uu____85299  ->
                       fun elt  ->
                         match uu____85299 with
                         | (g',inversions) ->
                             let uu____85327 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_85350  ->
                                       match uu___646_85350 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____85352;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____85353;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____85354;_}
                                           -> false
                                       | uu____85361 -> true))
                                in
                             (match uu____85327 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_85386 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_85386.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_85386.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_85386.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____85275 with
                 | (g',inversions) ->
                     let uu____85405 =
                       FStar_List.fold_left
                         (fun uu____85436  ->
                            fun elt  ->
                              match uu____85436 with
                              | (decls,elts,rest) ->
                                  let uu____85477 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_85486  ->
                                            match uu___647_85486 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____85488 -> true
                                            | uu____85501 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____85477
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____85524 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_85545  ->
                                               match uu___648_85545 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____85547 -> true
                                               | uu____85560 -> false))
                                        in
                                     match uu____85524 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_85591 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_85591.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_85591.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_85591.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____85405 with
                      | (decls,elts,rest) ->
                          let uu____85617 =
                            let uu____85618 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____85625 =
                              let uu____85628 =
                                let uu____85631 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____85631  in
                              FStar_List.append elts uu____85628  in
                            FStar_List.append uu____85618 uu____85625  in
                          (uu____85617, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,uu____85639,tps,k,uu____85642,datas) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let is_logical =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___649_85661  ->
                     match uu___649_85661 with
                     | FStar_Syntax_Syntax.Logic  -> true
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____85665 -> false))
              in
           let constructor_or_logic_type_decl c =
             if is_logical
             then
               let uu____85678 = c  in
               match uu____85678 with
               | (name,args,uu____85683,uu____85684,uu____85685) ->
                   let uu____85696 =
                     let uu____85697 =
                       let uu____85709 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____85736  ->
                                 match uu____85736 with
                                 | (uu____85745,sort,uu____85747) -> sort))
                          in
                       (name, uu____85709, FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                        in
                     FStar_SMTEncoding_Term.DeclFun uu____85697  in
                   [uu____85696]
             else
               (let uu____85758 = FStar_Ident.range_of_lid t  in
                FStar_SMTEncoding_Term.constructor_to_decl uu____85758 c)
              in
           let inversion_axioms tapp vars =
             let uu____85776 =
               FStar_All.pipe_right datas
                 (FStar_Util.for_some
                    (fun l  ->
                       let uu____85784 =
                         FStar_TypeChecker_Env.try_lookup_lid
                           env.FStar_SMTEncoding_Env.tcenv l
                          in
                       FStar_All.pipe_right uu____85784 FStar_Option.isNone))
                in
             if uu____85776
             then []
             else
               (let uu____85819 =
                  FStar_SMTEncoding_Env.fresh_fvar
                    env.FStar_SMTEncoding_Env.current_module_name "x"
                    FStar_SMTEncoding_Term.Term_sort
                   in
                match uu____85819 with
                | (xxsym,xx) ->
                    let uu____85832 =
                      FStar_All.pipe_right datas
                        (FStar_List.fold_left
                           (fun uu____85871  ->
                              fun l  ->
                                match uu____85871 with
                                | (out,decls) ->
                                    let uu____85891 =
                                      FStar_TypeChecker_Env.lookup_datacon
                                        env.FStar_SMTEncoding_Env.tcenv l
                                       in
                                    (match uu____85891 with
                                     | (uu____85902,data_t) ->
                                         let uu____85904 =
                                           FStar_Syntax_Util.arrow_formals
                                             data_t
                                            in
                                         (match uu____85904 with
                                          | (args,res) ->
                                              let indices =
                                                let uu____85948 =
                                                  let uu____85949 =
                                                    FStar_Syntax_Subst.compress
                                                      res
                                                     in
                                                  uu____85949.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____85948 with
                                                | FStar_Syntax_Syntax.Tm_app
                                                    (uu____85952,indices) ->
                                                    indices
                                                | uu____85978 -> []  in
                                              let env1 =
                                                FStar_All.pipe_right args
                                                  (FStar_List.fold_left
                                                     (fun env1  ->
                                                        fun uu____86008  ->
                                                          match uu____86008
                                                          with
                                                          | (x,uu____86016)
                                                              ->
                                                              let uu____86021
                                                                =
                                                                let uu____86022
                                                                  =
                                                                  let uu____86030
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                  (uu____86030,
                                                                    [xx])
                                                                   in
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  uu____86022
                                                                 in
                                                              FStar_SMTEncoding_Env.push_term_var
                                                                env1 x
                                                                uu____86021)
                                                     env)
                                                 in
                                              let uu____86035 =
                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                  indices env1
                                                 in
                                              (match uu____86035 with
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
                                                       let uu____86060 =
                                                         FStar_List.map2
                                                           (fun v1  ->
                                                              fun a  ->
                                                                let uu____86068
                                                                  =
                                                                  let uu____86073
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                  (uu____86073,
                                                                    a)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____86068)
                                                           vars indices1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____86060
                                                         FStar_SMTEncoding_Util.mk_and_l
                                                        in
                                                     let uu____86076 =
                                                       let uu____86077 =
                                                         let uu____86082 =
                                                           let uu____86083 =
                                                             let uu____86088
                                                               =
                                                               FStar_SMTEncoding_Env.mk_data_tester
                                                                 env1 l xx
                                                                in
                                                             (uu____86088,
                                                               eqs)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____86083
                                                            in
                                                         (out, uu____86082)
                                                          in
                                                       FStar_SMTEncoding_Util.mkOr
                                                         uu____86077
                                                        in
                                                     (uu____86076,
                                                       (FStar_List.append
                                                          decls decls'))))))))
                           (FStar_SMTEncoding_Util.mkFalse, []))
                       in
                    (match uu____85832 with
                     | (data_ax,decls) ->
                         let uu____86101 =
                           FStar_SMTEncoding_Env.fresh_fvar
                             env.FStar_SMTEncoding_Env.current_module_name
                             "f" FStar_SMTEncoding_Term.Fuel_sort
                            in
                         (match uu____86101 with
                          | (ffsym,ff) ->
                              let fuel_guarded_inversion =
                                let xx_has_type_sfuel =
                                  if
                                    (FStar_List.length datas) >
                                      (Prims.parse_int "1")
                                  then
                                    let uu____86118 =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [ff])
                                       in
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel
                                      uu____86118 xx tapp
                                  else
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                      xx tapp
                                   in
                                let uu____86125 =
                                  let uu____86133 =
                                    let uu____86134 =
                                      FStar_Ident.range_of_lid t  in
                                    let uu____86135 =
                                      let uu____86146 =
                                        let uu____86147 =
                                          FStar_SMTEncoding_Term.mk_fv
                                            (ffsym,
                                              FStar_SMTEncoding_Term.Fuel_sort)
                                           in
                                        let uu____86149 =
                                          let uu____86152 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          uu____86152 :: vars  in
                                        FStar_SMTEncoding_Env.add_fuel
                                          uu____86147 uu____86149
                                         in
                                      let uu____86154 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (xx_has_type_sfuel, data_ax)
                                         in
                                      ([[xx_has_type_sfuel]], uu____86146,
                                        uu____86154)
                                       in
                                    FStar_SMTEncoding_Term.mkForall
                                      uu____86134 uu____86135
                                     in
                                  let uu____86163 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                      (Prims.op_Hat "fuel_guarded_inversion_"
                                         t.FStar_Ident.str)
                                     in
                                  (uu____86133,
                                    (FStar_Pervasives_Native.Some
                                       "inversion axiom"), uu____86163)
                                   in
                                FStar_SMTEncoding_Util.mkAssume uu____86125
                                 in
                              let uu____86169 =
                                FStar_All.pipe_right [fuel_guarded_inversion]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              FStar_List.append decls uu____86169)))
              in
           let uu____86176 =
             let uu____86181 =
               let uu____86182 = FStar_Syntax_Subst.compress k  in
               uu____86182.FStar_Syntax_Syntax.n  in
             match uu____86181 with
             | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                 ((FStar_List.append tps formals),
                   (FStar_Syntax_Util.comp_result kres))
             | uu____86217 -> (tps, k)  in
           (match uu____86176 with
            | (formals,res) ->
                let uu____86224 = FStar_Syntax_Subst.open_term formals res
                   in
                (match uu____86224 with
                 | (formals1,res1) ->
                     let uu____86235 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals1 env
                        in
                     (match uu____86235 with
                      | (vars,guards,env',binder_decls,uu____86260) ->
                          let arity = FStar_List.length vars  in
                          let uu____86274 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env t arity
                             in
                          (match uu____86274 with
                           | (tname,ttok,env1) ->
                               let ttok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let tapp =
                                 let uu____86304 =
                                   let uu____86312 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, uu____86312)  in
                                 FStar_SMTEncoding_Util.mkApp uu____86304  in
                               let uu____86318 =
                                 let tname_decl =
                                   let uu____86328 =
                                     let uu____86329 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun fv  ->
                                               let uu____86348 =
                                                 let uu____86350 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     fv
                                                    in
                                                 Prims.op_Hat tname
                                                   uu____86350
                                                  in
                                               let uu____86352 =
                                                 FStar_SMTEncoding_Term.fv_sort
                                                   fv
                                                  in
                                               (uu____86348, uu____86352,
                                                 false)))
                                        in
                                     let uu____86356 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     (tname, uu____86329,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       uu____86356, false)
                                      in
                                   constructor_or_logic_type_decl uu____86328
                                    in
                                 let uu____86364 =
                                   match vars with
                                   | [] ->
                                       let uu____86377 =
                                         let uu____86378 =
                                           let uu____86381 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tname, [])
                                              in
                                           FStar_All.pipe_left
                                             (fun _86387  ->
                                                FStar_Pervasives_Native.Some
                                                  _86387) uu____86381
                                            in
                                         FStar_SMTEncoding_Env.push_free_var
                                           env1 t arity tname uu____86378
                                          in
                                       ([], uu____86377)
                                   | uu____86394 ->
                                       let ttok_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (ttok, [],
                                             FStar_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token"))
                                          in
                                       let ttok_fresh =
                                         let uu____86404 =
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                             ()
                                            in
                                         FStar_SMTEncoding_Term.fresh_token
                                           (ttok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                           uu____86404
                                          in
                                       let ttok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars
                                          in
                                       let pats = [[ttok_app]; [tapp]]  in
                                       let name_tok_corr =
                                         let uu____86420 =
                                           let uu____86428 =
                                             let uu____86429 =
                                               FStar_Ident.range_of_lid t  in
                                             let uu____86430 =
                                               let uu____86446 =
                                                 FStar_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp)
                                                  in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 vars, uu____86446)
                                                in
                                             FStar_SMTEncoding_Term.mkForall'
                                               uu____86429 uu____86430
                                              in
                                           (uu____86428,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.op_Hat
                                                "token_correspondence_" ttok))
                                            in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____86420
                                          in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env1)
                                    in
                                 match uu____86364 with
                                 | (tok_decls,env2) ->
                                     let uu____86473 =
                                       FStar_Ident.lid_equals t
                                         FStar_Parser_Const.lex_t_lid
                                        in
                                     if uu____86473
                                     then (tok_decls, env2)
                                     else
                                       ((FStar_List.append tname_decl
                                           tok_decls), env2)
                                  in
                               (match uu____86318 with
                                | (decls,env2) ->
                                    let kindingAx =
                                      let uu____86501 =
                                        FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res1
                                          env' tapp
                                         in
                                      match uu____86501 with
                                      | (k1,decls1) ->
                                          let karr =
                                            if
                                              (FStar_List.length formals1) >
                                                (Prims.parse_int "0")
                                            then
                                              let uu____86523 =
                                                let uu____86524 =
                                                  let uu____86532 =
                                                    let uu____86533 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____86533
                                                     in
                                                  (uu____86532,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.op_Hat
                                                       "pre_kinding_" ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____86524
                                                 in
                                              [uu____86523]
                                            else []  in
                                          let uu____86541 =
                                            let uu____86544 =
                                              let uu____86547 =
                                                let uu____86550 =
                                                  let uu____86551 =
                                                    let uu____86559 =
                                                      let uu____86560 =
                                                        FStar_Ident.range_of_lid
                                                          t
                                                         in
                                                      let uu____86561 =
                                                        let uu____86572 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____86572)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____86560
                                                        uu____86561
                                                       in
                                                    (uu____86559,
                                                      FStar_Pervasives_Native.None,
                                                      (Prims.op_Hat
                                                         "kinding_" ttok))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____86551
                                                   in
                                                [uu____86550]  in
                                              FStar_List.append karr
                                                uu____86547
                                               in
                                            FStar_All.pipe_right uu____86544
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          FStar_List.append decls1
                                            uu____86541
                                       in
                                    let aux =
                                      let uu____86591 =
                                        let uu____86594 =
                                          inversion_axioms tapp vars  in
                                        let uu____86597 =
                                          let uu____86600 =
                                            let uu____86603 =
                                              let uu____86604 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              pretype_axiom uu____86604 env2
                                                tapp vars
                                               in
                                            [uu____86603]  in
                                          FStar_All.pipe_right uu____86600
                                            FStar_SMTEncoding_Term.mk_decls_trivial
                                           in
                                        FStar_List.append uu____86594
                                          uu____86597
                                         in
                                      FStar_List.append kindingAx uu____86591
                                       in
                                    let g =
                                      let uu____86612 =
                                        FStar_All.pipe_right decls
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append uu____86612
                                        (FStar_List.append binder_decls aux)
                                       in
                                    (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____86620,uu____86621,uu____86622,uu____86623,uu____86624)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____86632,t,uu____86634,n_tps,uu____86636) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____86646 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____86646 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____86694 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____86694 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____86722 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____86722 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____86742 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____86742 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____86821 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____86821,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____86828 =
                                   let uu____86829 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____86829, true)
                                    in
                                 let uu____86837 =
                                   let uu____86844 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____86844
                                    in
                                 FStar_All.pipe_right uu____86828 uu____86837
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
                               let uu____86856 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____86856 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____86868::uu____86869 ->
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
                                            let uu____86918 =
                                              let uu____86919 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____86919]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____86918
                                             in
                                          let uu____86945 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____86946 =
                                            let uu____86957 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____86957)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____86945 uu____86946
                                      | uu____86984 -> tok_typing  in
                                    let uu____86995 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____86995 with
                                     | (vars',guards',env'',decls_formals,uu____87020)
                                         ->
                                         let uu____87033 =
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
                                         (match uu____87033 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____87063 ->
                                                    let uu____87072 =
                                                      let uu____87073 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____87073
                                                       in
                                                    [uu____87072]
                                                 in
                                              let encode_elim uu____87089 =
                                                let uu____87090 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____87090 with
                                                | (head1,args) ->
                                                    let uu____87141 =
                                                      let uu____87142 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____87142.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____87141 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____87154;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____87155;_},uu____87156)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____87162 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____87162
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
                                                                  | uu____87225
                                                                    ->
                                                                    let uu____87226
                                                                    =
                                                                    let uu____87232
                                                                    =
                                                                    let uu____87234
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____87234
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____87232)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____87226
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____87257
                                                                    =
                                                                    let uu____87259
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____87259
                                                                     in
                                                                    if
                                                                    uu____87257
                                                                    then
                                                                    let uu____87281
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____87281]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____87284
                                                                =
                                                                let uu____87298
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____87355
                                                                     ->
                                                                    fun
                                                                    uu____87356
                                                                     ->
                                                                    match 
                                                                    (uu____87355,
                                                                    uu____87356)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____87467
                                                                    =
                                                                    let uu____87475
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____87475
                                                                     in
                                                                    (match uu____87467
                                                                    with
                                                                    | 
                                                                    (uu____87489,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____87500
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____87500
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____87505
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____87505
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
                                                                  uu____87298
                                                                 in
                                                              (match uu____87284
                                                               with
                                                               | (uu____87526,arg_vars,elim_eqns_or_guards,uu____87529)
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
                                                                    let uu____87556
                                                                    =
                                                                    let uu____87564
                                                                    =
                                                                    let uu____87565
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____87566
                                                                    =
                                                                    let uu____87577
                                                                    =
                                                                    let uu____87578
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____87578
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____87580
                                                                    =
                                                                    let uu____87581
                                                                    =
                                                                    let uu____87586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____87586)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____87581
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____87577,
                                                                    uu____87580)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____87565
                                                                    uu____87566
                                                                     in
                                                                    (uu____87564,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____87556
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____87601
                                                                    =
                                                                    let uu____87602
                                                                    =
                                                                    let uu____87608
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____87608,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____87602
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____87601
                                                                     in
                                                                    let uu____87611
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____87611
                                                                    then
                                                                    let x =
                                                                    let uu____87615
                                                                    =
                                                                    let uu____87621
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____87621,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____87615
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____87626
                                                                    =
                                                                    let uu____87634
                                                                    =
                                                                    let uu____87635
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____87636
                                                                    =
                                                                    let uu____87647
                                                                    =
                                                                    let uu____87652
                                                                    =
                                                                    let uu____87655
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____87655]
                                                                     in
                                                                    [uu____87652]
                                                                     in
                                                                    let uu____87660
                                                                    =
                                                                    let uu____87661
                                                                    =
                                                                    let uu____87666
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____87668
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____87666,
                                                                    uu____87668)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____87661
                                                                     in
                                                                    (uu____87647,
                                                                    [x],
                                                                    uu____87660)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____87635
                                                                    uu____87636
                                                                     in
                                                                    let uu____87689
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____87634,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____87689)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____87626
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____87700
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
                                                                    (let uu____87723
                                                                    =
                                                                    let uu____87724
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____87724
                                                                    dapp1  in
                                                                    [uu____87723])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____87700
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____87731
                                                                    =
                                                                    let uu____87739
                                                                    =
                                                                    let uu____87740
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____87741
                                                                    =
                                                                    let uu____87752
                                                                    =
                                                                    let uu____87753
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____87753
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____87755
                                                                    =
                                                                    let uu____87756
                                                                    =
                                                                    let uu____87761
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____87761)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____87756
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____87752,
                                                                    uu____87755)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____87740
                                                                    uu____87741
                                                                     in
                                                                    (uu____87739,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____87731)
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
                                                         let uu____87780 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____87780
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
                                                                  | uu____87843
                                                                    ->
                                                                    let uu____87844
                                                                    =
                                                                    let uu____87850
                                                                    =
                                                                    let uu____87852
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____87852
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____87850)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____87844
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____87875
                                                                    =
                                                                    let uu____87877
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____87877
                                                                     in
                                                                    if
                                                                    uu____87875
                                                                    then
                                                                    let uu____87899
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____87899]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____87902
                                                                =
                                                                let uu____87916
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____87973
                                                                     ->
                                                                    fun
                                                                    uu____87974
                                                                     ->
                                                                    match 
                                                                    (uu____87973,
                                                                    uu____87974)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88085
                                                                    =
                                                                    let uu____88093
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88093
                                                                     in
                                                                    (match uu____88085
                                                                    with
                                                                    | 
                                                                    (uu____88107,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88118
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88118
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88123
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88123
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
                                                                  uu____87916
                                                                 in
                                                              (match uu____87902
                                                               with
                                                               | (uu____88144,arg_vars,elim_eqns_or_guards,uu____88147)
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
                                                                    let uu____88174
                                                                    =
                                                                    let uu____88182
                                                                    =
                                                                    let uu____88183
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88184
                                                                    =
                                                                    let uu____88195
                                                                    =
                                                                    let uu____88196
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88196
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88198
                                                                    =
                                                                    let uu____88199
                                                                    =
                                                                    let uu____88204
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88204)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88199
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88195,
                                                                    uu____88198)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88183
                                                                    uu____88184
                                                                     in
                                                                    (uu____88182,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88174
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88219
                                                                    =
                                                                    let uu____88220
                                                                    =
                                                                    let uu____88226
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88226,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88220
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88219
                                                                     in
                                                                    let uu____88229
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88229
                                                                    then
                                                                    let x =
                                                                    let uu____88233
                                                                    =
                                                                    let uu____88239
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88239,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88233
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88244
                                                                    =
                                                                    let uu____88252
                                                                    =
                                                                    let uu____88253
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88254
                                                                    =
                                                                    let uu____88265
                                                                    =
                                                                    let uu____88270
                                                                    =
                                                                    let uu____88273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88273]
                                                                     in
                                                                    [uu____88270]
                                                                     in
                                                                    let uu____88278
                                                                    =
                                                                    let uu____88279
                                                                    =
                                                                    let uu____88284
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88286
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88284,
                                                                    uu____88286)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88279
                                                                     in
                                                                    (uu____88265,
                                                                    [x],
                                                                    uu____88278)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88253
                                                                    uu____88254
                                                                     in
                                                                    let uu____88307
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88252,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88307)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88244
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88318
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
                                                                    (let uu____88341
                                                                    =
                                                                    let uu____88342
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88342
                                                                    dapp1  in
                                                                    [uu____88341])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88318
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88349
                                                                    =
                                                                    let uu____88357
                                                                    =
                                                                    let uu____88358
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88359
                                                                    =
                                                                    let uu____88370
                                                                    =
                                                                    let uu____88371
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88371
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88373
                                                                    =
                                                                    let uu____88374
                                                                    =
                                                                    let uu____88379
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88379)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88374
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88370,
                                                                    uu____88373)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88358
                                                                    uu____88359
                                                                     in
                                                                    (uu____88357,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88349)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____88396 ->
                                                         ((let uu____88398 =
                                                             let uu____88404
                                                               =
                                                               let uu____88406
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____88408
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____88406
                                                                 uu____88408
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____88404)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____88398);
                                                          ([], [])))
                                                 in
                                              let uu____88416 =
                                                encode_elim ()  in
                                              (match uu____88416 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____88442 =
                                                       let uu____88445 =
                                                         let uu____88448 =
                                                           let uu____88451 =
                                                             let uu____88454
                                                               =
                                                               let uu____88457
                                                                 =
                                                                 let uu____88460
                                                                   =
                                                                   let uu____88461
                                                                    =
                                                                    let uu____88473
                                                                    =
                                                                    let uu____88474
                                                                    =
                                                                    let uu____88476
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____88476
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____88474
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____88473)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____88461
                                                                    in
                                                                 [uu____88460]
                                                                  in
                                                               FStar_List.append
                                                                 uu____88457
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____88454
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____88487 =
                                                             let uu____88490
                                                               =
                                                               let uu____88493
                                                                 =
                                                                 let uu____88496
                                                                   =
                                                                   let uu____88499
                                                                    =
                                                                    let uu____88502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____88507
                                                                    =
                                                                    let uu____88510
                                                                    =
                                                                    let uu____88511
                                                                    =
                                                                    let uu____88519
                                                                    =
                                                                    let uu____88520
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88521
                                                                    =
                                                                    let uu____88532
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____88532)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88520
                                                                    uu____88521
                                                                     in
                                                                    (uu____88519,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88511
                                                                     in
                                                                    let uu____88545
                                                                    =
                                                                    let uu____88548
                                                                    =
                                                                    let uu____88549
                                                                    =
                                                                    let uu____88557
                                                                    =
                                                                    let uu____88558
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88559
                                                                    =
                                                                    let uu____88570
                                                                    =
                                                                    let uu____88571
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88571
                                                                    vars'  in
                                                                    let uu____88573
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____88570,
                                                                    uu____88573)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88558
                                                                    uu____88559
                                                                     in
                                                                    (uu____88557,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88549
                                                                     in
                                                                    [uu____88548]
                                                                     in
                                                                    uu____88510
                                                                    ::
                                                                    uu____88545
                                                                     in
                                                                    uu____88502
                                                                    ::
                                                                    uu____88507
                                                                     in
                                                                   FStar_List.append
                                                                    uu____88499
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____88496
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____88493
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____88490
                                                              in
                                                           FStar_List.append
                                                             uu____88451
                                                             uu____88487
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____88448
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____88445
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____88442
                                                      in
                                                   let uu____88590 =
                                                     let uu____88591 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____88591 g
                                                      in
                                                   (uu____88590, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____88625  ->
              fun se  ->
                match uu____88625 with
                | (g,env1) ->
                    let uu____88645 = encode_sigelt env1 se  in
                    (match uu____88645 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____88713 =
        match uu____88713 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____88750 ->
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
                 ((let uu____88758 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____88758
                   then
                     let uu____88763 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____88765 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____88767 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____88763 uu____88765 uu____88767
                   else ());
                  (let uu____88772 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____88772 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____88790 =
                         let uu____88798 =
                           let uu____88800 =
                             let uu____88802 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____88802
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____88800  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____88798
                          in
                       (match uu____88790 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____88822 = FStar_Options.log_queries ()
                                 in
                              if uu____88822
                              then
                                let uu____88825 =
                                  let uu____88827 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____88829 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____88831 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____88827 uu____88829 uu____88831
                                   in
                                FStar_Pervasives_Native.Some uu____88825
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____88847 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____88857 =
                                let uu____88860 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____88860  in
                              FStar_List.append uu____88847 uu____88857  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____88872,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____88892 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____88892 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____88913 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____88913 with | (uu____88940,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____88993  ->
              match uu____88993 with
              | (l,uu____89002,uu____89003) ->
                  let uu____89006 =
                    let uu____89018 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____89018, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____89006))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____89051  ->
              match uu____89051 with
              | (l,uu____89062,uu____89063) ->
                  let uu____89066 =
                    let uu____89067 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _89070  -> FStar_SMTEncoding_Term.Echo _89070)
                      uu____89067
                     in
                  let uu____89071 =
                    let uu____89074 =
                      let uu____89075 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____89075  in
                    [uu____89074]  in
                  uu____89066 :: uu____89071))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____89104 =
      let uu____89107 =
        let uu____89108 = FStar_Util.psmap_empty ()  in
        let uu____89123 =
          let uu____89132 = FStar_Util.psmap_empty ()  in (uu____89132, [])
           in
        let uu____89139 =
          let uu____89141 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____89141 FStar_Ident.string_of_lid  in
        let uu____89143 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____89108;
          FStar_SMTEncoding_Env.fvar_bindings = uu____89123;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____89139;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____89143
        }  in
      [uu____89107]  in
    FStar_ST.op_Colon_Equals last_env uu____89104
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____89187 = FStar_ST.op_Bang last_env  in
      match uu____89187 with
      | [] -> failwith "No env; call init first!"
      | e::uu____89215 ->
          let uu___2089_89218 = e  in
          let uu____89219 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2089_89218.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2089_89218.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2089_89218.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2089_89218.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2089_89218.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2089_89218.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2089_89218.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____89219;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2089_89218.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2089_89218.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____89227 = FStar_ST.op_Bang last_env  in
    match uu____89227 with
    | [] -> failwith "Empty env stack"
    | uu____89254::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____89286  ->
    let uu____89287 = FStar_ST.op_Bang last_env  in
    match uu____89287 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____89347  ->
    let uu____89348 = FStar_ST.op_Bang last_env  in
    match uu____89348 with
    | [] -> failwith "Popping an empty stack"
    | uu____89375::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____89412  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____89465  ->
         let uu____89466 = snapshot_env ()  in
         match uu____89466 with
         | (env_depth,()) ->
             let uu____89488 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____89488 with
              | (varops_depth,()) ->
                  let uu____89510 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____89510 with
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
        (fun uu____89568  ->
           let uu____89569 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____89569 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____89664 = snapshot msg  in () 
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
        | (uu____89710::uu____89711,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2150_89719 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2150_89719.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2150_89719.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2150_89719.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____89720 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2156_89747 = elt  in
        let uu____89748 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2156_89747.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2156_89747.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____89748;
          FStar_SMTEncoding_Term.a_names =
            (uu___2156_89747.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____89768 =
        let uu____89771 =
          let uu____89772 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____89772  in
        let uu____89773 = open_fact_db_tags env  in uu____89771 ::
          uu____89773
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____89768
  
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
      let uu____89800 = encode_sigelt env se  in
      match uu____89800 with
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
                (let uu____89846 =
                   let uu____89849 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____89849
                    in
                 match uu____89846 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____89864 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____89864
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____89894 = FStar_Options.log_queries ()  in
        if uu____89894
        then
          let uu____89899 =
            let uu____89900 =
              let uu____89902 =
                let uu____89904 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____89904 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____89902  in
            FStar_SMTEncoding_Term.Caption uu____89900  in
          uu____89899 :: decls
        else decls  in
      (let uu____89923 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____89923
       then
         let uu____89926 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____89926
       else ());
      (let env =
         let uu____89932 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____89932 tcenv  in
       let uu____89933 = encode_top_level_facts env se  in
       match uu____89933 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____89947 =
               let uu____89950 =
                 let uu____89953 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____89953
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____89950  in
             FStar_SMTEncoding_Z3.giveZ3 uu____89947)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____89986 = FStar_Options.log_queries ()  in
          if uu____89986
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2194_90006 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2194_90006.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2194_90006.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2194_90006.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2194_90006.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2194_90006.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2194_90006.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2194_90006.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2194_90006.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2194_90006.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2194_90006.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____90011 =
             let uu____90014 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____90014
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____90011  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____90034 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____90034
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
          (let uu____90058 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____90058
           then
             let uu____90061 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____90061
           else ());
          (let env =
             let uu____90069 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____90069
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____90108  ->
                     fun se  ->
                       match uu____90108 with
                       | (g,env2) ->
                           let uu____90128 = encode_top_level_facts env2 se
                              in
                           (match uu____90128 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____90151 =
             encode_signature
               (let uu___2217_90160 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2217_90160.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2217_90160.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2217_90160.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2217_90160.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2217_90160.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2217_90160.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2217_90160.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2217_90160.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2217_90160.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2217_90160.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____90151 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____90176 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____90176
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____90182 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____90182))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____90210  ->
        match uu____90210 with
        | (decls,fvbs) ->
            ((let uu____90224 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____90224
              then ()
              else
                (let uu____90229 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____90229
                 then
                   let uu____90232 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____90232
                 else ()));
             (let env =
                let uu____90240 = get_env name tcenv  in
                FStar_All.pipe_right uu____90240
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____90242 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____90242
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____90256 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____90256
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
        (let uu____90318 =
           let uu____90320 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____90320.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____90318);
        (let env =
           let uu____90322 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____90322 tcenv  in
         let uu____90323 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____90362 = aux rest  in
                 (match uu____90362 with
                  | (out,rest1) ->
                      let t =
                        let uu____90390 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____90390 with
                        | FStar_Pervasives_Native.Some uu____90393 ->
                            let uu____90394 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____90394
                              x.FStar_Syntax_Syntax.sort
                        | uu____90395 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____90399 =
                        let uu____90402 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2258_90405 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2258_90405.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2258_90405.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____90402 :: out  in
                      (uu____90399, rest1))
             | uu____90410 -> ([], bindings)  in
           let uu____90417 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____90417 with
           | (closing,bindings) ->
               let uu____90444 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____90444, bindings)
            in
         match uu____90323 with
         | (q1,bindings) ->
             let uu____90475 = encode_env_bindings env bindings  in
             (match uu____90475 with
              | (env_decls,env1) ->
                  ((let uu____90497 =
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
                    if uu____90497
                    then
                      let uu____90504 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____90504
                    else ());
                   (let uu____90509 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____90509 with
                    | (phi,qdecls) ->
                        let uu____90530 =
                          let uu____90535 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____90535 phi
                           in
                        (match uu____90530 with
                         | (labels,phi1) ->
                             let uu____90552 = encode_labels labels  in
                             (match uu____90552 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____90588 =
                                      FStar_Options.log_queries ()  in
                                    if uu____90588
                                    then
                                      let uu____90593 =
                                        let uu____90594 =
                                          let uu____90596 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____90596
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____90594
                                         in
                                      [uu____90593]
                                    else []  in
                                  let query_prelude =
                                    let uu____90604 =
                                      let uu____90605 =
                                        let uu____90606 =
                                          let uu____90609 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____90616 =
                                            let uu____90619 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____90619
                                             in
                                          FStar_List.append uu____90609
                                            uu____90616
                                           in
                                        FStar_List.append env_decls
                                          uu____90606
                                         in
                                      FStar_All.pipe_right uu____90605
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____90604
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____90629 =
                                      let uu____90637 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____90638 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____90637,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____90638)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____90629
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
  