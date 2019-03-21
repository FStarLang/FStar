open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]  in
      FStar_TypeChecker_Normalize.normalize steps
        env.FStar_SMTEncoding_Env.tcenv t
  
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
  let uu____67926 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67926 with
  | (asym,a) ->
      let uu____67937 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67937 with
       | (xsym,x) ->
           let uu____67948 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67948 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____68026 =
                      let uu____68038 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____68038, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____68026  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68058 =
                      let uu____68066 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68066)  in
                    FStar_SMTEncoding_Util.mkApp uu____68058  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68085 =
                    let uu____68088 =
                      let uu____68091 =
                        let uu____68094 =
                          let uu____68095 =
                            let uu____68103 =
                              let uu____68104 =
                                let uu____68115 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68115)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68104
                               in
                            (uu____68103, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68095  in
                        let uu____68127 =
                          let uu____68130 =
                            let uu____68131 =
                              let uu____68139 =
                                let uu____68140 =
                                  let uu____68151 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68151)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68140
                                 in
                              (uu____68139,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68131  in
                          [uu____68130]  in
                        uu____68094 :: uu____68127  in
                      xtok_decl :: uu____68091  in
                    xname_decl :: uu____68088  in
                  (xtok1, (FStar_List.length vars), uu____68085)  in
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
                  let uu____68321 =
                    let uu____68342 =
                      let uu____68361 =
                        let uu____68362 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68362
                         in
                      quant axy uu____68361  in
                    (FStar_Parser_Const.op_Eq, uu____68342)  in
                  let uu____68379 =
                    let uu____68402 =
                      let uu____68423 =
                        let uu____68442 =
                          let uu____68443 =
                            let uu____68444 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68444  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68443
                           in
                        quant axy uu____68442  in
                      (FStar_Parser_Const.op_notEq, uu____68423)  in
                    let uu____68461 =
                      let uu____68484 =
                        let uu____68505 =
                          let uu____68524 =
                            let uu____68525 =
                              let uu____68526 =
                                let uu____68531 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68532 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68531, uu____68532)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68526  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68525
                             in
                          quant xy uu____68524  in
                        (FStar_Parser_Const.op_And, uu____68505)  in
                      let uu____68549 =
                        let uu____68572 =
                          let uu____68593 =
                            let uu____68612 =
                              let uu____68613 =
                                let uu____68614 =
                                  let uu____68619 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68620 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68619, uu____68620)  in
                                FStar_SMTEncoding_Util.mkOr uu____68614  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68613
                               in
                            quant xy uu____68612  in
                          (FStar_Parser_Const.op_Or, uu____68593)  in
                        let uu____68637 =
                          let uu____68660 =
                            let uu____68681 =
                              let uu____68700 =
                                let uu____68701 =
                                  let uu____68702 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68702
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68701
                                 in
                              quant qx uu____68700  in
                            (FStar_Parser_Const.op_Negation, uu____68681)  in
                          let uu____68719 =
                            let uu____68742 =
                              let uu____68763 =
                                let uu____68782 =
                                  let uu____68783 =
                                    let uu____68784 =
                                      let uu____68789 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68790 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68789, uu____68790)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68784
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68783
                                   in
                                quant xy uu____68782  in
                              (FStar_Parser_Const.op_LT, uu____68763)  in
                            let uu____68807 =
                              let uu____68830 =
                                let uu____68851 =
                                  let uu____68870 =
                                    let uu____68871 =
                                      let uu____68872 =
                                        let uu____68877 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68878 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68877, uu____68878)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68872
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68871
                                     in
                                  quant xy uu____68870  in
                                (FStar_Parser_Const.op_LTE, uu____68851)  in
                              let uu____68895 =
                                let uu____68918 =
                                  let uu____68939 =
                                    let uu____68958 =
                                      let uu____68959 =
                                        let uu____68960 =
                                          let uu____68965 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68966 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68965, uu____68966)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68960
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68959
                                       in
                                    quant xy uu____68958  in
                                  (FStar_Parser_Const.op_GT, uu____68939)  in
                                let uu____68983 =
                                  let uu____69006 =
                                    let uu____69027 =
                                      let uu____69046 =
                                        let uu____69047 =
                                          let uu____69048 =
                                            let uu____69053 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69054 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69053, uu____69054)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69048
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69047
                                         in
                                      quant xy uu____69046  in
                                    (FStar_Parser_Const.op_GTE, uu____69027)
                                     in
                                  let uu____69071 =
                                    let uu____69094 =
                                      let uu____69115 =
                                        let uu____69134 =
                                          let uu____69135 =
                                            let uu____69136 =
                                              let uu____69141 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69142 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69141, uu____69142)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69136
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69135
                                           in
                                        quant xy uu____69134  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69115)
                                       in
                                    let uu____69159 =
                                      let uu____69182 =
                                        let uu____69203 =
                                          let uu____69222 =
                                            let uu____69223 =
                                              let uu____69224 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69224
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69223
                                             in
                                          quant qx uu____69222  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69203)
                                         in
                                      let uu____69241 =
                                        let uu____69264 =
                                          let uu____69285 =
                                            let uu____69304 =
                                              let uu____69305 =
                                                let uu____69306 =
                                                  let uu____69311 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69312 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69311, uu____69312)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69306
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69305
                                               in
                                            quant xy uu____69304  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69285)
                                           in
                                        let uu____69329 =
                                          let uu____69352 =
                                            let uu____69373 =
                                              let uu____69392 =
                                                let uu____69393 =
                                                  let uu____69394 =
                                                    let uu____69399 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69400 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69399,
                                                      uu____69400)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69394
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69393
                                                 in
                                              quant xy uu____69392  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69373)
                                             in
                                          let uu____69417 =
                                            let uu____69440 =
                                              let uu____69461 =
                                                let uu____69480 =
                                                  let uu____69481 =
                                                    let uu____69482 =
                                                      let uu____69487 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69488 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69487,
                                                        uu____69488)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69482
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69481
                                                   in
                                                quant xy uu____69480  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69461)
                                               in
                                            let uu____69505 =
                                              let uu____69528 =
                                                let uu____69549 =
                                                  let uu____69568 =
                                                    let uu____69569 =
                                                      let uu____69570 =
                                                        let uu____69575 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69576 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69575,
                                                          uu____69576)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69570
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69569
                                                     in
                                                  quant xy uu____69568  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69549)
                                                 in
                                              let uu____69593 =
                                                let uu____69616 =
                                                  let uu____69637 =
                                                    let uu____69656 =
                                                      let uu____69657 =
                                                        let uu____69658 =
                                                          let uu____69663 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69664 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69663,
                                                            uu____69664)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69658
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69657
                                                       in
                                                    quant xy uu____69656  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69637)
                                                   in
                                                let uu____69681 =
                                                  let uu____69704 =
                                                    let uu____69725 =
                                                      let uu____69744 =
                                                        let uu____69745 =
                                                          let uu____69746 =
                                                            let uu____69751 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69752 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69751,
                                                              uu____69752)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69746
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69745
                                                         in
                                                      quant xy uu____69744
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69725)
                                                     in
                                                  let uu____69769 =
                                                    let uu____69792 =
                                                      let uu____69813 =
                                                        let uu____69832 =
                                                          let uu____69833 =
                                                            let uu____69834 =
                                                              let uu____69839
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69840
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69839,
                                                                uu____69840)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69834
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69833
                                                           in
                                                        quant xy uu____69832
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69813)
                                                       in
                                                    let uu____69857 =
                                                      let uu____69880 =
                                                        let uu____69901 =
                                                          let uu____69920 =
                                                            let uu____69921 =
                                                              let uu____69922
                                                                =
                                                                let uu____69927
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69928
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69927,
                                                                  uu____69928)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69922
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69921
                                                             in
                                                          quant xy
                                                            uu____69920
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69901)
                                                         in
                                                      let uu____69945 =
                                                        let uu____69968 =
                                                          let uu____69989 =
                                                            let uu____70008 =
                                                              let uu____70009
                                                                =
                                                                let uu____70010
                                                                  =
                                                                  let uu____70015
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____70016
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____70015,
                                                                    uu____70016)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____70010
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____70009
                                                               in
                                                            quant xy
                                                              uu____70008
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69989)
                                                           in
                                                        let uu____70033 =
                                                          let uu____70056 =
                                                            let uu____70077 =
                                                              let uu____70096
                                                                =
                                                                let uu____70097
                                                                  =
                                                                  let uu____70098
                                                                    =
                                                                    let uu____70103
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70104
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70103,
                                                                    uu____70104)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70098
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70097
                                                                 in
                                                              quant xy
                                                                uu____70096
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70077)
                                                             in
                                                          let uu____70121 =
                                                            let uu____70144 =
                                                              let uu____70165
                                                                =
                                                                let uu____70184
                                                                  =
                                                                  let uu____70185
                                                                    =
                                                                    let uu____70186
                                                                    =
                                                                    let uu____70191
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70192
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70191,
                                                                    uu____70192)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70186
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70185
                                                                   in
                                                                quant xy
                                                                  uu____70184
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70165)
                                                               in
                                                            let uu____70209 =
                                                              let uu____70232
                                                                =
                                                                let uu____70253
                                                                  =
                                                                  let uu____70272
                                                                    =
                                                                    let uu____70273
                                                                    =
                                                                    let uu____70274
                                                                    =
                                                                    let uu____70279
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70280
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70279,
                                                                    uu____70280)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70274
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70273
                                                                     in
                                                                  quant xy
                                                                    uu____70272
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70253)
                                                                 in
                                                              let uu____70297
                                                                =
                                                                let uu____70320
                                                                  =
                                                                  let uu____70341
                                                                    =
                                                                    let uu____70360
                                                                    =
                                                                    let uu____70361
                                                                    =
                                                                    let uu____70362
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70362
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70361
                                                                     in
                                                                    quant qx
                                                                    uu____70360
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70341)
                                                                   in
                                                                [uu____70320]
                                                                 in
                                                              uu____70232 ::
                                                                uu____70297
                                                               in
                                                            uu____70144 ::
                                                              uu____70209
                                                             in
                                                          uu____70056 ::
                                                            uu____70121
                                                           in
                                                        uu____69968 ::
                                                          uu____70033
                                                         in
                                                      uu____69880 ::
                                                        uu____69945
                                                       in
                                                    uu____69792 ::
                                                      uu____69857
                                                     in
                                                  uu____69704 :: uu____69769
                                                   in
                                                uu____69616 :: uu____69681
                                                 in
                                              uu____69528 :: uu____69593  in
                                            uu____69440 :: uu____69505  in
                                          uu____69352 :: uu____69417  in
                                        uu____69264 :: uu____69329  in
                                      uu____69182 :: uu____69241  in
                                    uu____69094 :: uu____69159  in
                                  uu____69006 :: uu____69071  in
                                uu____68918 :: uu____68983  in
                              uu____68830 :: uu____68895  in
                            uu____68742 :: uu____68807  in
                          uu____68660 :: uu____68719  in
                        uu____68572 :: uu____68637  in
                      uu____68484 :: uu____68549  in
                    uu____68402 :: uu____68461  in
                  uu____68321 :: uu____68379  in
                let mk1 l v1 =
                  let uu____70901 =
                    let uu____70913 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____71003  ->
                              match uu____71003 with
                              | (l',uu____71024) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70913
                      (FStar_Option.map
                         (fun uu____71123  ->
                            match uu____71123 with
                            | (uu____71151,b) ->
                                let uu____71185 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71185 v1))
                     in
                  FStar_All.pipe_right uu____70901 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71268  ->
                          match uu____71268 with
                          | (l',uu____71289) -> FStar_Ident.lid_equals l l'))
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
          let uu____71363 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71363 with
          | (xxsym,xx) ->
              let uu____71374 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71374 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71390 =
                     let uu____71398 =
                       let uu____71399 =
                         let uu____71410 =
                           let uu____71411 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71421 =
                             let uu____71432 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71432 :: vars  in
                           uu____71411 :: uu____71421  in
                         let uu____71458 =
                           let uu____71459 =
                             let uu____71464 =
                               let uu____71465 =
                                 let uu____71470 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71470)  in
                               FStar_SMTEncoding_Util.mkEq uu____71465  in
                             (xx_has_type, uu____71464)  in
                           FStar_SMTEncoding_Util.mkImp uu____71459  in
                         ([[xx_has_type]], uu____71410, uu____71458)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71399  in
                     let uu____71483 =
                       let uu____71485 =
                         let uu____71487 =
                           let uu____71489 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71489  in
                         Prims.op_Hat module_name uu____71487  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71485
                        in
                     (uu____71398,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71483)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71390)
  
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
    let uu____71545 =
      let uu____71547 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71547  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71545  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71569 =
      let uu____71570 =
        let uu____71578 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71578, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71570  in
    let uu____71583 =
      let uu____71586 =
        let uu____71587 =
          let uu____71595 =
            let uu____71596 =
              let uu____71607 =
                let uu____71608 =
                  let uu____71613 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71613)  in
                FStar_SMTEncoding_Util.mkImp uu____71608  in
              ([[typing_pred]], [xx], uu____71607)  in
            let uu____71638 =
              let uu____71653 = FStar_TypeChecker_Env.get_range env  in
              let uu____71654 = mkForall_fuel1 env  in
              uu____71654 uu____71653  in
            uu____71638 uu____71596  in
          (uu____71595, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71587  in
      [uu____71586]  in
    uu____71569 :: uu____71583  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71701 =
      let uu____71702 =
        let uu____71710 =
          let uu____71711 = FStar_TypeChecker_Env.get_range env  in
          let uu____71712 =
            let uu____71723 =
              let uu____71728 =
                let uu____71731 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71731]  in
              [uu____71728]  in
            let uu____71736 =
              let uu____71737 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71737 tt  in
            (uu____71723, [bb], uu____71736)  in
          FStar_SMTEncoding_Term.mkForall uu____71711 uu____71712  in
        (uu____71710, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71702  in
    let uu____71762 =
      let uu____71765 =
        let uu____71766 =
          let uu____71774 =
            let uu____71775 =
              let uu____71786 =
                let uu____71787 =
                  let uu____71792 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71792)  in
                FStar_SMTEncoding_Util.mkImp uu____71787  in
              ([[typing_pred]], [xx], uu____71786)  in
            let uu____71819 =
              let uu____71834 = FStar_TypeChecker_Env.get_range env  in
              let uu____71835 = mkForall_fuel1 env  in
              uu____71835 uu____71834  in
            uu____71819 uu____71775  in
          (uu____71774, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71766  in
      [uu____71765]  in
    uu____71701 :: uu____71762  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71878 =
        let uu____71879 =
          let uu____71885 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71885, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71879  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71878  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71899 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71899  in
    let uu____71904 =
      let uu____71905 =
        let uu____71913 =
          let uu____71914 = FStar_TypeChecker_Env.get_range env  in
          let uu____71915 =
            let uu____71926 =
              let uu____71931 =
                let uu____71934 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71934]  in
              [uu____71931]  in
            let uu____71939 =
              let uu____71940 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71940 tt  in
            (uu____71926, [bb], uu____71939)  in
          FStar_SMTEncoding_Term.mkForall uu____71914 uu____71915  in
        (uu____71913, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71905  in
    let uu____71965 =
      let uu____71968 =
        let uu____71969 =
          let uu____71977 =
            let uu____71978 =
              let uu____71989 =
                let uu____71990 =
                  let uu____71995 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71995)  in
                FStar_SMTEncoding_Util.mkImp uu____71990  in
              ([[typing_pred]], [xx], uu____71989)  in
            let uu____72022 =
              let uu____72037 = FStar_TypeChecker_Env.get_range env  in
              let uu____72038 = mkForall_fuel1 env  in
              uu____72038 uu____72037  in
            uu____72022 uu____71978  in
          (uu____71977, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71969  in
      let uu____72060 =
        let uu____72063 =
          let uu____72064 =
            let uu____72072 =
              let uu____72073 =
                let uu____72084 =
                  let uu____72085 =
                    let uu____72090 =
                      let uu____72091 =
                        let uu____72094 =
                          let uu____72097 =
                            let uu____72100 =
                              let uu____72101 =
                                let uu____72106 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72107 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72106, uu____72107)  in
                              FStar_SMTEncoding_Util.mkGT uu____72101  in
                            let uu____72109 =
                              let uu____72112 =
                                let uu____72113 =
                                  let uu____72118 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72119 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72118, uu____72119)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72113  in
                              let uu____72121 =
                                let uu____72124 =
                                  let uu____72125 =
                                    let uu____72130 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72131 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72130, uu____72131)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72125  in
                                [uu____72124]  in
                              uu____72112 :: uu____72121  in
                            uu____72100 :: uu____72109  in
                          typing_pred_y :: uu____72097  in
                        typing_pred :: uu____72094  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72091  in
                    (uu____72090, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72085  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72084)
                 in
              let uu____72164 =
                let uu____72179 = FStar_TypeChecker_Env.get_range env  in
                let uu____72180 = mkForall_fuel1 env  in
                uu____72180 uu____72179  in
              uu____72164 uu____72073  in
            (uu____72072,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72064  in
        [uu____72063]  in
      uu____71968 :: uu____72060  in
    uu____71904 :: uu____71965  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72223 =
        let uu____72224 =
          let uu____72230 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72230, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72224  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72223  in
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
      let uu____72246 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72246  in
    let uu____72251 =
      let uu____72252 =
        let uu____72260 =
          let uu____72261 = FStar_TypeChecker_Env.get_range env  in
          let uu____72262 =
            let uu____72273 =
              let uu____72278 =
                let uu____72281 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72281]  in
              [uu____72278]  in
            let uu____72286 =
              let uu____72287 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72287 tt  in
            (uu____72273, [bb], uu____72286)  in
          FStar_SMTEncoding_Term.mkForall uu____72261 uu____72262  in
        (uu____72260, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72252  in
    let uu____72312 =
      let uu____72315 =
        let uu____72316 =
          let uu____72324 =
            let uu____72325 =
              let uu____72336 =
                let uu____72337 =
                  let uu____72342 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72342)  in
                FStar_SMTEncoding_Util.mkImp uu____72337  in
              ([[typing_pred]], [xx], uu____72336)  in
            let uu____72369 =
              let uu____72384 = FStar_TypeChecker_Env.get_range env  in
              let uu____72385 = mkForall_fuel1 env  in
              uu____72385 uu____72384  in
            uu____72369 uu____72325  in
          (uu____72324, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72316  in
      let uu____72407 =
        let uu____72410 =
          let uu____72411 =
            let uu____72419 =
              let uu____72420 =
                let uu____72431 =
                  let uu____72432 =
                    let uu____72437 =
                      let uu____72438 =
                        let uu____72441 =
                          let uu____72444 =
                            let uu____72447 =
                              let uu____72448 =
                                let uu____72453 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72454 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72453, uu____72454)  in
                              FStar_SMTEncoding_Util.mkGT uu____72448  in
                            let uu____72456 =
                              let uu____72459 =
                                let uu____72460 =
                                  let uu____72465 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72466 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72465, uu____72466)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72460  in
                              let uu____72468 =
                                let uu____72471 =
                                  let uu____72472 =
                                    let uu____72477 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72478 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72477, uu____72478)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72472  in
                                [uu____72471]  in
                              uu____72459 :: uu____72468  in
                            uu____72447 :: uu____72456  in
                          typing_pred_y :: uu____72444  in
                        typing_pred :: uu____72441  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72438  in
                    (uu____72437, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72432  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72431)
                 in
              let uu____72511 =
                let uu____72526 = FStar_TypeChecker_Env.get_range env  in
                let uu____72527 = mkForall_fuel1 env  in
                uu____72527 uu____72526  in
              uu____72511 uu____72420  in
            (uu____72419,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72411  in
        [uu____72410]  in
      uu____72315 :: uu____72407  in
    uu____72251 :: uu____72312  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72574 =
      let uu____72575 =
        let uu____72583 =
          let uu____72584 = FStar_TypeChecker_Env.get_range env  in
          let uu____72585 =
            let uu____72596 =
              let uu____72601 =
                let uu____72604 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72604]  in
              [uu____72601]  in
            let uu____72609 =
              let uu____72610 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72610 tt  in
            (uu____72596, [bb], uu____72609)  in
          FStar_SMTEncoding_Term.mkForall uu____72584 uu____72585  in
        (uu____72583, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72575  in
    let uu____72635 =
      let uu____72638 =
        let uu____72639 =
          let uu____72647 =
            let uu____72648 =
              let uu____72659 =
                let uu____72660 =
                  let uu____72665 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72665)  in
                FStar_SMTEncoding_Util.mkImp uu____72660  in
              ([[typing_pred]], [xx], uu____72659)  in
            let uu____72692 =
              let uu____72707 = FStar_TypeChecker_Env.get_range env  in
              let uu____72708 = mkForall_fuel1 env  in
              uu____72708 uu____72707  in
            uu____72692 uu____72648  in
          (uu____72647, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72639  in
      [uu____72638]  in
    uu____72574 :: uu____72635  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72755 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72755]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72785 =
      let uu____72786 =
        let uu____72794 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72794, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72786  in
    [uu____72785]  in
  let mk_and_interp env conj uu____72817 =
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
    let uu____72846 =
      let uu____72847 =
        let uu____72855 =
          let uu____72856 = FStar_TypeChecker_Env.get_range env  in
          let uu____72857 =
            let uu____72868 =
              let uu____72869 =
                let uu____72874 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72874, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72869  in
            ([[l_and_a_b]], [aa; bb], uu____72868)  in
          FStar_SMTEncoding_Term.mkForall uu____72856 uu____72857  in
        (uu____72855, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72847  in
    [uu____72846]  in
  let mk_or_interp env disj uu____72929 =
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
    let uu____72958 =
      let uu____72959 =
        let uu____72967 =
          let uu____72968 = FStar_TypeChecker_Env.get_range env  in
          let uu____72969 =
            let uu____72980 =
              let uu____72981 =
                let uu____72986 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72986, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72981  in
            ([[l_or_a_b]], [aa; bb], uu____72980)  in
          FStar_SMTEncoding_Term.mkForall uu____72968 uu____72969  in
        (uu____72967, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72959  in
    [uu____72958]  in
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
    let uu____73064 =
      let uu____73065 =
        let uu____73073 =
          let uu____73074 = FStar_TypeChecker_Env.get_range env  in
          let uu____73075 =
            let uu____73086 =
              let uu____73087 =
                let uu____73092 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73092, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73087  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73086)  in
          FStar_SMTEncoding_Term.mkForall uu____73074 uu____73075  in
        (uu____73073, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73065  in
    [uu____73064]  in
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
    let uu____73182 =
      let uu____73183 =
        let uu____73191 =
          let uu____73192 = FStar_TypeChecker_Env.get_range env  in
          let uu____73193 =
            let uu____73204 =
              let uu____73205 =
                let uu____73210 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73210, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73205  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73204)  in
          FStar_SMTEncoding_Term.mkForall uu____73192 uu____73193  in
        (uu____73191, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73183  in
    [uu____73182]  in
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
    let uu____73310 =
      let uu____73311 =
        let uu____73319 =
          let uu____73320 = FStar_TypeChecker_Env.get_range env  in
          let uu____73321 =
            let uu____73332 =
              let uu____73333 =
                let uu____73338 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73338, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73333  in
            ([[l_imp_a_b]], [aa; bb], uu____73332)  in
          FStar_SMTEncoding_Term.mkForall uu____73320 uu____73321  in
        (uu____73319, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73311  in
    [uu____73310]  in
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
    let uu____73422 =
      let uu____73423 =
        let uu____73431 =
          let uu____73432 = FStar_TypeChecker_Env.get_range env  in
          let uu____73433 =
            let uu____73444 =
              let uu____73445 =
                let uu____73450 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73450, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73445  in
            ([[l_iff_a_b]], [aa; bb], uu____73444)  in
          FStar_SMTEncoding_Term.mkForall uu____73432 uu____73433  in
        (uu____73431, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73423  in
    [uu____73422]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73521 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73521  in
    let uu____73526 =
      let uu____73527 =
        let uu____73535 =
          let uu____73536 = FStar_TypeChecker_Env.get_range env  in
          let uu____73537 =
            let uu____73548 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73548)  in
          FStar_SMTEncoding_Term.mkForall uu____73536 uu____73537  in
        (uu____73535, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73527  in
    [uu____73526]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73601 =
      let uu____73602 =
        let uu____73610 =
          let uu____73611 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73611 range_ty  in
        let uu____73612 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73610, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73612)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73602  in
    [uu____73601]  in
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
        let uu____73658 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73658 x1 t  in
      let uu____73660 = FStar_TypeChecker_Env.get_range env  in
      let uu____73661 =
        let uu____73672 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73672)  in
      FStar_SMTEncoding_Term.mkForall uu____73660 uu____73661  in
    let uu____73697 =
      let uu____73698 =
        let uu____73706 =
          let uu____73707 = FStar_TypeChecker_Env.get_range env  in
          let uu____73708 =
            let uu____73719 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73719)  in
          FStar_SMTEncoding_Term.mkForall uu____73707 uu____73708  in
        (uu____73706,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73698  in
    [uu____73697]  in
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
    let uu____73780 =
      let uu____73781 =
        let uu____73789 =
          let uu____73790 = FStar_TypeChecker_Env.get_range env  in
          let uu____73791 =
            let uu____73807 =
              let uu____73808 =
                let uu____73813 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73814 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73813, uu____73814)  in
              FStar_SMTEncoding_Util.mkAnd uu____73808  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73807)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73790 uu____73791  in
        (uu____73789,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73781  in
    [uu____73780]  in
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
          let uu____74372 =
            FStar_Util.find_opt
              (fun uu____74410  ->
                 match uu____74410 with
                 | (l,uu____74426) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74372 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74469,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74530 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74530 with
        | (form,decls) ->
            let uu____74539 =
              let uu____74542 =
                let uu____74545 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74545]  in
              FStar_All.pipe_right uu____74542
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74539
  
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
              let uu____74604 =
                ((let uu____74608 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74608) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74604
              then
                let arg_sorts =
                  let uu____74620 =
                    let uu____74621 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74621.FStar_Syntax_Syntax.n  in
                  match uu____74620 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74627) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74665  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74672 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74674 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74674 with
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
                    let uu____74706 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74706, env1)
              else
                (let uu____74711 = prims.is lid  in
                 if uu____74711
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74720 = prims.mk lid vname  in
                   match uu____74720 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74744 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74744, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74753 =
                      let uu____74772 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74772 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74800 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74800
                            then
                              let uu____74805 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___934_74808 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___934_74808.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___934_74808.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___934_74808.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___934_74808.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___934_74808.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___934_74808.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___934_74808.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___934_74808.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___934_74808.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___934_74808.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___934_74808.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___934_74808.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___934_74808.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___934_74808.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___934_74808.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___934_74808.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___934_74808.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___934_74808.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___934_74808.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___934_74808.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___934_74808.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___934_74808.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___934_74808.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___934_74808.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___934_74808.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___934_74808.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___934_74808.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___934_74808.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___934_74808.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___934_74808.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___934_74808.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___934_74808.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___934_74808.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___934_74808.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___934_74808.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___934_74808.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___934_74808.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___934_74808.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___934_74808.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___934_74808.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___934_74808.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___934_74808.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74805
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74831 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74831)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74753 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74937  ->
                                  match uu___639_74937 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74941 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74941 with
                                       | (uu____74974,xxv) ->
                                           let xx =
                                             let uu____75013 =
                                               let uu____75014 =
                                                 let uu____75020 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75020,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75014
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75013
                                              in
                                           let uu____75023 =
                                             let uu____75024 =
                                               let uu____75032 =
                                                 let uu____75033 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75034 =
                                                   let uu____75045 =
                                                     let uu____75046 =
                                                       let uu____75051 =
                                                         let uu____75052 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75052
                                                          in
                                                       (vapp, uu____75051)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75046
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75045)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75033 uu____75034
                                                  in
                                               (uu____75032,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75024
                                              in
                                           [uu____75023])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75067 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75067 with
                                       | (uu____75100,xxv) ->
                                           let xx =
                                             let uu____75139 =
                                               let uu____75140 =
                                                 let uu____75146 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75146,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75140
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75139
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
                                           let uu____75157 =
                                             let uu____75158 =
                                               let uu____75166 =
                                                 let uu____75167 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75168 =
                                                   let uu____75179 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75179)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75167 uu____75168
                                                  in
                                               (uu____75166,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75158
                                              in
                                           [uu____75157])
                                  | uu____75192 -> []))
                           in
                        let uu____75193 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75193 with
                         | (vars,guards,env',decls1,uu____75218) ->
                             let uu____75231 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75244 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75244, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75248 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75248 with
                                    | (g,ds) ->
                                        let uu____75261 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75261,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75231 with
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
                                  let should_thunk uu____75284 =
                                    let is_type1 t =
                                      let uu____75292 =
                                        let uu____75293 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75293.FStar_Syntax_Syntax.n  in
                                      match uu____75292 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75297 -> true
                                      | uu____75299 -> false  in
                                    let is_squash1 t =
                                      let uu____75308 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75308 with
                                      | (head1,uu____75327) ->
                                          let uu____75352 =
                                            let uu____75353 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75353.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75352 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75358;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75359;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75361;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75362;_};_},uu____75363)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75371 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75376 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75376))
                                       &&
                                       (let uu____75382 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75382))
                                      &&
                                      (let uu____75385 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75385)
                                     in
                                  let uu____75387 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75446 -> (false, vars)  in
                                  (match uu____75387 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75496 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75496 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75528 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75537 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75537
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75548 ->
                                                  let uu____75557 =
                                                    let uu____75565 =
                                                      get_vtok ()  in
                                                    (uu____75565, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75557
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75572 =
                                                let uu____75580 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75580)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75572
                                               in
                                            let uu____75594 =
                                              let vname_decl =
                                                let uu____75602 =
                                                  let uu____75614 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75614,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75602
                                                 in
                                              let uu____75625 =
                                                let env2 =
                                                  let uu___1029_75631 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1029_75631.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75632 =
                                                  let uu____75634 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75634
                                                   in
                                                if uu____75632
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75625 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75651 =
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
                                                        let uu____75677 =
                                                          let uu____75680 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75680
                                                           in
                                                        let uu____75687 =
                                                          let uu____75688 =
                                                            let uu____75691 =
                                                              let uu____75692
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75692
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75696  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75696)
                                                              uu____75691
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75688
                                                           in
                                                        (uu____75677,
                                                          uu____75687)
                                                    | uu____75699 when
                                                        thunked ->
                                                        let uu____75710 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75710
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75725
                                                                 =
                                                                 let uu____75733
                                                                   =
                                                                   let uu____75736
                                                                    =
                                                                    let uu____75739
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75739]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75736
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75733)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75725
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75747
                                                               =
                                                               let uu____75755
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75755,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75747
                                                              in
                                                           let uu____75760 =
                                                             let uu____75763
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75763
                                                              in
                                                           (uu____75760,
                                                             env1))
                                                    | uu____75772 ->
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
                                                          let uu____75796 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75797 =
                                                            let uu____75808 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75808)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75796
                                                            uu____75797
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75818 =
                                                            let uu____75826 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75826,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75818
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
                                                            let uu____75837 =
                                                              let uu____75838
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75838]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75837
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75865 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75866 =
                                                              let uu____75877
                                                                =
                                                                let uu____75878
                                                                  =
                                                                  let uu____75883
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75884
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75883,
                                                                    uu____75884)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75878
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75877)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75865
                                                              uu____75866
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75913 =
                                                          let uu____75916 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75916
                                                           in
                                                        (uu____75913, env1)
                                                     in
                                                  (match uu____75651 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75937 =
                                                         let uu____75940 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75940
                                                           tok_decl
                                                          in
                                                       (uu____75937, env2))
                                               in
                                            (match uu____75594 with
                                             | (decls2,env2) ->
                                                 let uu____75959 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75969 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75969 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75984 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75984, decls)
                                                    in
                                                 (match uu____75959 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____75999 =
                                                          let uu____76007 =
                                                            let uu____76008 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76009 =
                                                              let uu____76020
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____76020)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____76008
                                                              uu____76009
                                                             in
                                                          (uu____76007,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____75999
                                                         in
                                                      let freshness =
                                                        let uu____76036 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____76036
                                                        then
                                                          let uu____76044 =
                                                            let uu____76045 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76046 =
                                                              let uu____76059
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76066
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76059,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76066)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____76045
                                                              uu____76046
                                                             in
                                                          let uu____76072 =
                                                            let uu____76075 =
                                                              let uu____76076
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76076
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76075]  in
                                                          uu____76044 ::
                                                            uu____76072
                                                        else []  in
                                                      let g =
                                                        let uu____76082 =
                                                          let uu____76085 =
                                                            let uu____76088 =
                                                              let uu____76091
                                                                =
                                                                let uu____76094
                                                                  =
                                                                  let uu____76097
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76097
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76094
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76091
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76088
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76085
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76082
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
          let uu____76137 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76137 with
          | FStar_Pervasives_Native.None  ->
              let uu____76148 = encode_free_var false env x t t_norm []  in
              (match uu____76148 with
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
            let tt = norm_before_encoding env t  in
            let uu____76211 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76211 with
            | (decls,env1) ->
                let uu____76222 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76222
                then
                  let uu____76229 =
                    let uu____76230 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76230  in
                  (uu____76229, env1)
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
             (fun uu____76286  ->
                fun lb  ->
                  match uu____76286 with
                  | (decls,env1) ->
                      let uu____76306 =
                        let uu____76311 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76311
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76306 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76340 = FStar_Syntax_Util.head_and_args t  in
    match uu____76340 with
    | (hd1,args) ->
        let uu____76384 =
          let uu____76385 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76385.FStar_Syntax_Syntax.n  in
        (match uu____76384 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76391,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76415 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76426 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1116_76434 = en  in
    let uu____76435 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1116_76434.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1116_76434.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1116_76434.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1116_76434.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1116_76434.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1116_76434.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1116_76434.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1116_76434.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1116_76434.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1116_76434.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76435
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76465  ->
      fun quals  ->
        match uu____76465 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76570 = FStar_Util.first_N nbinders formals  in
              match uu____76570 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76667  ->
                         fun uu____76668  ->
                           match (uu____76667, uu____76668) with
                           | ((formal,uu____76694),(binder,uu____76696)) ->
                               let uu____76717 =
                                 let uu____76724 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76724)  in
                               FStar_Syntax_Syntax.NT uu____76717) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76738 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76779  ->
                              match uu____76779 with
                              | (x,i) ->
                                  let uu____76798 =
                                    let uu___1142_76799 = x  in
                                    let uu____76800 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1142_76799.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1142_76799.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76800
                                    }  in
                                  (uu____76798, i)))
                       in
                    FStar_All.pipe_right uu____76738
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76824 =
                      let uu____76829 = FStar_Syntax_Subst.compress body  in
                      let uu____76830 =
                        let uu____76831 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76831
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76829
                        uu____76830
                       in
                    uu____76824 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1149_76880 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1149_76880.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1149_76880.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1149_76880.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1149_76880.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1149_76880.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1149_76880.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1149_76880.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1149_76880.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1149_76880.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1149_76880.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1149_76880.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1149_76880.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1149_76880.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1149_76880.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1149_76880.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1149_76880.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1149_76880.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1149_76880.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1149_76880.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1149_76880.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1149_76880.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1149_76880.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1149_76880.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1149_76880.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1149_76880.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1149_76880.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1149_76880.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1149_76880.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1149_76880.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1149_76880.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1149_76880.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1149_76880.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1149_76880.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1149_76880.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1149_76880.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1149_76880.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1149_76880.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1149_76880.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1149_76880.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1149_76880.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1149_76880.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1149_76880.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76952  ->
                       fun uu____76953  ->
                         match (uu____76952, uu____76953) with
                         | ((x,uu____76979),(b,uu____76981)) ->
                             let uu____77002 =
                               let uu____77009 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____77009)  in
                             FStar_Syntax_Syntax.NT uu____77002) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____77034 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____77034
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77063 ->
                    let uu____77070 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77070
                | uu____77071 when Prims.op_Negation norm1 ->
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
                | uu____77074 ->
                    let uu____77075 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77075)
                 in
              let aux t1 e1 =
                let uu____77117 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77117 with
                | (binders,body,lopt) ->
                    let uu____77149 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77165 -> arrow_formals_comp_norm false t1  in
                    (match uu____77149 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77199 =
                           if nformals < nbinders
                           then
                             let uu____77233 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77233 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77313 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77313)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77343 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77343 with
                                | (binders1,body1) ->
                                    let uu____77396 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77396))
                             else
                               (let uu____77409 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77409))
                            in
                         (match uu____77199 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77469 = aux t e  in
              match uu____77469 with
              | (binders,body,comp) ->
                  let uu____77515 =
                    let uu____77526 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77526
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77541 = aux comp1 body1  in
                      match uu____77541 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77515 with
                   | (binders1,body1,comp1) ->
                       let uu____77624 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77624, comp1))
               in
            (try
               (fun uu___1219_77651  ->
                  match () with
                  | () ->
                      let uu____77658 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77658
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77674 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77737  ->
                                   fun lb  ->
                                     match uu____77737 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77792 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77792
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77798 =
                                             let uu____77807 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77807
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77798 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77674 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77948;
                                    FStar_Syntax_Syntax.lbeff = uu____77949;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77951;
                                    FStar_Syntax_Syntax.lbpos = uu____77952;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77976 =
                                     let uu____77983 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77983 with
                                     | (tcenv',uu____77999,e_t) ->
                                         let uu____78005 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____78016 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____78005 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1282_78033 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1282_78033.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77976 with
                                    | (env',e1,t_norm1) ->
                                        let uu____78043 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____78043 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78063 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78063
                                               then
                                                 let uu____78068 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78071 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78068 uu____78071
                                               else ());
                                              (let uu____78076 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78076 with
                                               | (vars,_guards,env'1,binder_decls,uu____78103)
                                                   ->
                                                   let uu____78116 =
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
                                                         let uu____78133 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78133
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78155 =
                                                          let uu____78156 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78157 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78156 fvb
                                                            uu____78157
                                                           in
                                                        (vars, uu____78155))
                                                      in
                                                   (match uu____78116 with
                                                    | (vars1,app) ->
                                                        let uu____78168 =
                                                          let is_logical =
                                                            let uu____78181 =
                                                              let uu____78182
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78182.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78181
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78188 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78192 =
                                                              let uu____78193
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78193
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78192
                                                              (fun lid  ->
                                                                 let uu____78202
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78202
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78203 =
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
                                                          if uu____78203
                                                          then
                                                            let uu____78219 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78220 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78219,
                                                              uu____78220)
                                                          else
                                                            (let uu____78231
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78231))
                                                           in
                                                        (match uu____78168
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78255
                                                                 =
                                                                 let uu____78263
                                                                   =
                                                                   let uu____78264
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78265
                                                                    =
                                                                    let uu____78276
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78276)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78264
                                                                    uu____78265
                                                                    in
                                                                 let uu____78285
                                                                   =
                                                                   let uu____78286
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78286
                                                                    in
                                                                 (uu____78263,
                                                                   uu____78285,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78255
                                                                in
                                                             let uu____78292
                                                               =
                                                               let uu____78295
                                                                 =
                                                                 let uu____78298
                                                                   =
                                                                   let uu____78301
                                                                    =
                                                                    let uu____78304
                                                                    =
                                                                    let uu____78307
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78307
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78304
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78301
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78298
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78295
                                                                in
                                                             (uu____78292,
                                                               env2)))))))
                               | uu____78316 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78376 =
                                   let uu____78382 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78382,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78376  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78388 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78441  ->
                                         fun fvb  ->
                                           match uu____78441 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78496 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78496
                                                  in
                                               let gtok =
                                                 let uu____78500 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78500
                                                  in
                                               let env4 =
                                                 let uu____78503 =
                                                   let uu____78506 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78512  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78512) uu____78506
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78503
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78388 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78632
                                     t_norm uu____78634 =
                                     match (uu____78632, uu____78634) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78664;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78665;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78667;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78668;_})
                                         ->
                                         let uu____78695 =
                                           let uu____78702 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78702 with
                                           | (tcenv',uu____78718,e_t) ->
                                               let uu____78724 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78735 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78724 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1369_78752 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1369_78752.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78695 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78765 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78765
                                                then
                                                  let uu____78770 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78772 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78774 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78770 uu____78772
                                                    uu____78774
                                                else ());
                                               (let uu____78779 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78779 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78806 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78806 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78828 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78828
                                                           then
                                                             let uu____78833
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78835
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78838
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78840
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78833
                                                               uu____78835
                                                               uu____78838
                                                               uu____78840
                                                           else ());
                                                          (let uu____78845 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78845
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78874)
                                                               ->
                                                               let uu____78887
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78900,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78904
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78904
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78917
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78917,
                                                                    decls0))
                                                                  in
                                                               (match uu____78887
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
                                                                    let uu____78938
                                                                    =
                                                                    let uu____78950
                                                                    =
                                                                    let uu____78953
                                                                    =
                                                                    let uu____78956
                                                                    =
                                                                    let uu____78959
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78959
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78956
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78953
                                                                     in
                                                                    (g,
                                                                    uu____78950,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78938
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
                                                                    let uu____78989
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78989
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
                                                                    let uu____79004
                                                                    =
                                                                    let uu____79007
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____79007
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79004
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____79013
                                                                    =
                                                                    let uu____79016
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____79016
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79013
                                                                     in
                                                                    let uu____79021
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____79021
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____79037
                                                                    =
                                                                    let uu____79045
                                                                    =
                                                                    let uu____79046
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79047
                                                                    =
                                                                    let uu____79063
                                                                    =
                                                                    let uu____79064
                                                                    =
                                                                    let uu____79069
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79069)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79064
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79063)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79046
                                                                    uu____79047
                                                                     in
                                                                    let uu____79083
                                                                    =
                                                                    let uu____79084
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79084
                                                                     in
                                                                    (uu____79045,
                                                                    uu____79083,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79037
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79091
                                                                    =
                                                                    let uu____79099
                                                                    =
                                                                    let uu____79100
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79101
                                                                    =
                                                                    let uu____79112
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79112)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79100
                                                                    uu____79101
                                                                     in
                                                                    (uu____79099,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79091
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79126
                                                                    =
                                                                    let uu____79134
                                                                    =
                                                                    let uu____79135
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79136
                                                                    =
                                                                    let uu____79147
                                                                    =
                                                                    let uu____79148
                                                                    =
                                                                    let uu____79153
                                                                    =
                                                                    let uu____79154
                                                                    =
                                                                    let uu____79157
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79157
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79154
                                                                     in
                                                                    (gsapp,
                                                                    uu____79153)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79148
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79147)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79135
                                                                    uu____79136
                                                                     in
                                                                    (uu____79134,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79126
                                                                     in
                                                                    let uu____79171
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
                                                                    let uu____79183
                                                                    =
                                                                    let uu____79184
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79184
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79183
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79186
                                                                    =
                                                                    let uu____79194
                                                                    =
                                                                    let uu____79195
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79196
                                                                    =
                                                                    let uu____79207
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79207)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79195
                                                                    uu____79196
                                                                     in
                                                                    (uu____79194,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79186
                                                                     in
                                                                    let uu____79220
                                                                    =
                                                                    let uu____79229
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79229
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79244
                                                                    =
                                                                    let uu____79247
                                                                    =
                                                                    let uu____79248
                                                                    =
                                                                    let uu____79256
                                                                    =
                                                                    let uu____79257
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79258
                                                                    =
                                                                    let uu____79269
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79269)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79257
                                                                    uu____79258
                                                                     in
                                                                    (uu____79256,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79248
                                                                     in
                                                                    [uu____79247]
                                                                     in
                                                                    (d3,
                                                                    uu____79244)
                                                                     in
                                                                    match uu____79220
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79171
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79326
                                                                    =
                                                                    let uu____79329
                                                                    =
                                                                    let uu____79332
                                                                    =
                                                                    let uu____79335
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79335
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79332
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79329
                                                                     in
                                                                    let uu____79342
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79326,
                                                                    uu____79342,
                                                                    env02))))))))))
                                      in
                                   let uu____79347 =
                                     let uu____79360 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79423  ->
                                          fun uu____79424  ->
                                            match (uu____79423, uu____79424)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79549 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79549 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79360
                                      in
                                   (match uu____79347 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79616 =
                                          let isDeclFun uu___640_79633 =
                                            match uu___640_79633 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79635 -> true
                                            | uu____79648 -> false  in
                                          let uu____79650 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79650
                                            (fun decls3  ->
                                               let uu____79680 =
                                                 FStar_List.fold_left
                                                   (fun uu____79711  ->
                                                      fun elt  ->
                                                        match uu____79711
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79752 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79752
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79780
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79780
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
                                                                    let uu___1462_79818
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1462_79818.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1462_79818.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1462_79818.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79680 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79850 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79850, elts, rest))
                                           in
                                        (match uu____79616 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79879 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79885  ->
                                        match uu___641_79885 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79888 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79896 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79896)))
                                in
                             if uu____79879
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1479_79918  ->
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
                   let uu____79957 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79957
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79976 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79976, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____80032 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____80032 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____80038 = encode_sigelt' env se  in
      match uu____80038 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80050 =
                  let uu____80053 =
                    let uu____80054 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80054  in
                  [uu____80053]  in
                FStar_All.pipe_right uu____80050
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80059 ->
                let uu____80060 =
                  let uu____80063 =
                    let uu____80066 =
                      let uu____80067 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80067  in
                    [uu____80066]  in
                  FStar_All.pipe_right uu____80063
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80074 =
                  let uu____80077 =
                    let uu____80080 =
                      let uu____80083 =
                        let uu____80084 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80084  in
                      [uu____80083]  in
                    FStar_All.pipe_right uu____80080
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80077  in
                FStar_List.append uu____80060 uu____80074
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80098 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80098
       then
         let uu____80103 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80103
       else ());
      (let is_opaque_to_smt t =
         let uu____80115 =
           let uu____80116 = FStar_Syntax_Subst.compress t  in
           uu____80116.FStar_Syntax_Syntax.n  in
         match uu____80115 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80121)) -> s = "opaque_to_smt"
         | uu____80126 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80135 =
           let uu____80136 = FStar_Syntax_Subst.compress t  in
           uu____80136.FStar_Syntax_Syntax.n  in
         match uu____80135 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80141)) -> s = "uninterpreted_by_smt"
         | uu____80146 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80152 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80158 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80170 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80171 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80172 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80185 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80187 =
             let uu____80189 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80189  in
           if uu____80187
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80218 ->
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
                let action_defn =
                  let uu____80251 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____80251  in
                let uu____80252 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80252 with
                | (formals,uu____80272) ->
                    let arity = FStar_List.length formals  in
                    let uu____80296 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80296 with
                     | (aname,atok,env2) ->
                         let uu____80318 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____80318 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80334 =
                                  let uu____80335 =
                                    let uu____80347 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80367  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80347,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80335
                                   in
                                [uu____80334;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80384 =
                                let aux uu____80430 uu____80431 =
                                  match (uu____80430, uu____80431) with
                                  | ((bv,uu____80475),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80507 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80507 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80530 =
                                             let uu____80533 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80533 :: acc_sorts  in
                                           (env4, uu____80530, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80384 with
                               | (uu____80565,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80581 =
                                       let uu____80589 =
                                         let uu____80590 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80591 =
                                           let uu____80602 =
                                             let uu____80603 =
                                               let uu____80608 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80608)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80603
                                              in
                                           ([[app]], xs_sorts, uu____80602)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80590 uu____80591
                                          in
                                       (uu____80589,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80581
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80623 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80623
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80626 =
                                       let uu____80634 =
                                         let uu____80635 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80636 =
                                           let uu____80647 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80647)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80635 uu____80636
                                          in
                                       (uu____80634,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80626
                                      in
                                   let uu____80660 =
                                     let uu____80663 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80663  in
                                   (env2, uu____80660))))
                 in
              let uu____80672 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80672 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80698,uu____80699)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80700 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80700 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80722,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80729 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80735  ->
                       match uu___642_80735 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80738 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80744 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80747 -> false))
                in
             Prims.op_Negation uu____80729  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80757 =
                let uu____80762 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80762 env fv t quals  in
              match uu____80757 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80776 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80776  in
                  let uu____80779 =
                    let uu____80780 =
                      let uu____80783 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80783
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80780  in
                  (uu____80779, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80793 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80793 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1616_80805 = env  in
                  let uu____80806 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1616_80805.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1616_80805.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1616_80805.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80806;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1616_80805.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1616_80805.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1616_80805.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1616_80805.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1616_80805.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1616_80805.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1616_80805.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____80808 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80808 with
                 | (f3,decls) ->
                     let g =
                       let uu____80822 =
                         let uu____80825 =
                           let uu____80826 =
                             let uu____80834 =
                               let uu____80835 =
                                 let uu____80837 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80837
                                  in
                               FStar_Pervasives_Native.Some uu____80835  in
                             let uu____80841 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80834, uu____80841)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80826  in
                         [uu____80825]  in
                       FStar_All.pipe_right uu____80822
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80850) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80864 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80886 =
                        let uu____80889 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80889.FStar_Syntax_Syntax.fv_name  in
                      uu____80886.FStar_Syntax_Syntax.v  in
                    let uu____80890 =
                      let uu____80892 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80892  in
                    if uu____80890
                    then
                      let val_decl =
                        let uu___1633_80924 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1633_80924.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1633_80924.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1633_80924.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80925 = encode_sigelt' env1 val_decl  in
                      match uu____80925 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80864 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80961,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80963;
                           FStar_Syntax_Syntax.lbtyp = uu____80964;
                           FStar_Syntax_Syntax.lbeff = uu____80965;
                           FStar_Syntax_Syntax.lbdef = uu____80966;
                           FStar_Syntax_Syntax.lbattrs = uu____80967;
                           FStar_Syntax_Syntax.lbpos = uu____80968;_}::[]),uu____80969)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80988 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80988 with
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
                  let uu____81026 =
                    let uu____81029 =
                      let uu____81030 =
                        let uu____81038 =
                          let uu____81039 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____81040 =
                            let uu____81051 =
                              let uu____81052 =
                                let uu____81057 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81057)  in
                              FStar_SMTEncoding_Util.mkEq uu____81052  in
                            ([[b2t_x]], [xx], uu____81051)  in
                          FStar_SMTEncoding_Term.mkForall uu____81039
                            uu____81040
                           in
                        (uu____81038,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____81030  in
                    [uu____81029]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____81026
                   in
                let uu____81095 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81095, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81098,uu____81099) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81109  ->
                   match uu___643_81109 with
                   | FStar_Syntax_Syntax.Discriminator uu____81111 -> true
                   | uu____81113 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81115,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81127 =
                      let uu____81129 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81129.FStar_Ident.idText  in
                    uu____81127 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81136  ->
                      match uu___644_81136 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81139 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81142) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81156  ->
                   match uu___645_81156 with
                   | FStar_Syntax_Syntax.Projector uu____81158 -> true
                   | uu____81164 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81168 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81168 with
            | FStar_Pervasives_Native.Some uu____81175 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1698_81177 = se  in
                  let uu____81178 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81178;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1698_81177.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1698_81177.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1698_81177.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81181) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1710_81202 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1710_81202.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1710_81202.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1710_81202.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1710_81202.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1710_81202.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81207) ->
           let uu____81216 = encode_sigelts env ses  in
           (match uu____81216 with
            | (g,env1) ->
                let uu____81227 =
                  FStar_List.fold_left
                    (fun uu____81251  ->
                       fun elt  ->
                         match uu____81251 with
                         | (g',inversions) ->
                             let uu____81279 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81302  ->
                                       match uu___646_81302 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81304;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81305;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81306;_}
                                           -> false
                                       | uu____81313 -> true))
                                in
                             (match uu____81279 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1736_81338 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1736_81338.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1736_81338.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1736_81338.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81227 with
                 | (g',inversions) ->
                     let uu____81357 =
                       FStar_List.fold_left
                         (fun uu____81388  ->
                            fun elt  ->
                              match uu____81388 with
                              | (decls,elts,rest) ->
                                  let uu____81429 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81438  ->
                                            match uu___647_81438 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81440 -> true
                                            | uu____81453 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81429
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81476 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81497  ->
                                               match uu___648_81497 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81499 -> true
                                               | uu____81512 -> false))
                                        in
                                     match uu____81476 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1758_81543 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1758_81543.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1758_81543.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1758_81543.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81357 with
                      | (decls,elts,rest) ->
                          let uu____81569 =
                            let uu____81570 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81577 =
                              let uu____81580 =
                                let uu____81583 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81583  in
                              FStar_List.append elts uu____81580  in
                            FStar_List.append uu____81570 uu____81577  in
                          (uu____81569, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81594,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81607 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81607 with
             | (usubst,uvs) ->
                 let uu____81627 =
                   let uu____81634 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81635 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81636 =
                     let uu____81637 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81637 k  in
                   (uu____81634, uu____81635, uu____81636)  in
                 (match uu____81627 with
                  | (env1,tps1,k1) ->
                      let uu____81650 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81650 with
                       | (tps2,k2) ->
                           let uu____81658 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81658 with
                            | (uu____81674,k3) ->
                                let uu____81696 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81696 with
                                 | (tps3,env_tps,uu____81708,us) ->
                                     let u_k =
                                       let uu____81711 =
                                         let uu____81712 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81713 =
                                           let uu____81718 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81720 =
                                             let uu____81721 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81721
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81718 uu____81720
                                            in
                                         uu____81713
                                           FStar_Pervasives_Native.None
                                           uu____81712
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81711 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81739) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81745,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81748) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81756,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81763) ->
                                           let uu____81764 =
                                             let uu____81766 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81766
                                              in
                                           failwith uu____81764
                                       | (uu____81770,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81771 =
                                             let uu____81773 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81773
                                              in
                                           failwith uu____81771
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81777,uu____81778) ->
                                           let uu____81787 =
                                             let uu____81789 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81789
                                              in
                                           failwith uu____81787
                                       | (uu____81793,FStar_Syntax_Syntax.U_unif
                                          uu____81794) ->
                                           let uu____81803 =
                                             let uu____81805 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81805
                                              in
                                           failwith uu____81803
                                       | uu____81809 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81822 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81822 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81840 = u_leq_u_k u_tp  in
                                       if uu____81840
                                       then true
                                       else
                                         (let uu____81847 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81847 with
                                          | (formals,uu____81864) ->
                                              let uu____81885 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81885 with
                                               | (uu____81895,uu____81896,uu____81897,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81908 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81908
             then
               let uu____81913 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81913
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81933  ->
                       match uu___649_81933 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81937 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81950 = c  in
                 match uu____81950 with
                 | (name,args,uu____81955,uu____81956,uu____81957) ->
                     let uu____81968 =
                       let uu____81969 =
                         let uu____81981 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____82008  ->
                                   match uu____82008 with
                                   | (uu____82017,sort,uu____82019) -> sort))
                            in
                         (name, uu____81981,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81969  in
                     [uu____81968]
               else
                 (let uu____82030 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____82030 c)
                in
             let inversion_axioms tapp vars =
               let uu____82048 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____82056 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____82056 FStar_Option.isNone))
                  in
               if uu____82048
               then []
               else
                 (let uu____82091 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82091 with
                  | (xxsym,xx) ->
                      let uu____82104 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82143  ->
                                fun l  ->
                                  match uu____82143 with
                                  | (out,decls) ->
                                      let uu____82163 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82163 with
                                       | (uu____82174,data_t) ->
                                           let uu____82176 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82176 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82220 =
                                                    let uu____82221 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82221.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82220 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82224,indices)
                                                      -> indices
                                                  | uu____82250 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82280  ->
                                                            match uu____82280
                                                            with
                                                            | (x,uu____82288)
                                                                ->
                                                                let uu____82293
                                                                  =
                                                                  let uu____82294
                                                                    =
                                                                    let uu____82302
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82302,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82294
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82293)
                                                       env)
                                                   in
                                                let uu____82307 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82307 with
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
                                                                  let uu____82342
                                                                    =
                                                                    let uu____82347
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82347,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82342)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82350 =
                                                         let uu____82351 =
                                                           let uu____82356 =
                                                             let uu____82357
                                                               =
                                                               let uu____82362
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82363
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82362,
                                                                 uu____82363)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82357
                                                              in
                                                           (out, uu____82356)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82351
                                                          in
                                                       (uu____82350,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82104 with
                       | (data_ax,decls) ->
                           let uu____82378 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82378 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82395 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82395 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82402 =
                                    let uu____82410 =
                                      let uu____82411 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82412 =
                                        let uu____82423 =
                                          let uu____82424 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82426 =
                                            let uu____82429 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82429 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82424 uu____82426
                                           in
                                        let uu____82431 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82423,
                                          uu____82431)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82411 uu____82412
                                       in
                                    let uu____82440 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82410,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82440)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82402
                                   in
                                let uu____82446 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82446)))
                in
             let uu____82453 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____82475 ->
                     let uu____82476 =
                       let uu____82483 =
                         let uu____82484 =
                           let uu____82499 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____82499)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____82484  in
                       FStar_Syntax_Syntax.mk uu____82483  in
                     uu____82476 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____82453 with
             | (formals,res) ->
                 let uu____82539 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____82539 with
                  | (vars,guards,env',binder_decls,uu____82564) ->
                      let arity = FStar_List.length vars  in
                      let uu____82578 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____82578 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____82604 =
                               let uu____82612 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____82612)  in
                             FStar_SMTEncoding_Util.mkApp uu____82604  in
                           let uu____82618 =
                             let tname_decl =
                               let uu____82628 =
                                 let uu____82629 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____82648 =
                                             let uu____82650 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____82650
                                              in
                                           let uu____82652 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____82648, uu____82652, false)))
                                    in
                                 let uu____82656 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____82629,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____82656, false)
                                  in
                               constructor_or_logic_type_decl uu____82628  in
                             let uu____82664 =
                               match vars with
                               | [] ->
                                   let uu____82677 =
                                     let uu____82678 =
                                       let uu____82681 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _82687  ->
                                            FStar_Pervasives_Native.Some
                                              _82687) uu____82681
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____82678
                                      in
                                   ([], uu____82677)
                               | uu____82690 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____82700 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____82700
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____82716 =
                                       let uu____82724 =
                                         let uu____82725 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____82726 =
                                           let uu____82742 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____82742)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____82725 uu____82726
                                          in
                                       (uu____82724,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____82716
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____82664 with
                             | (tok_decls,env2) ->
                                 let uu____82769 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____82769
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____82618 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____82797 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____82797 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____82819 =
                                            let uu____82820 =
                                              let uu____82828 =
                                                let uu____82829 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____82829
                                                 in
                                              (uu____82828,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____82820
                                             in
                                          [uu____82819]
                                        else []  in
                                      let uu____82837 =
                                        let uu____82840 =
                                          let uu____82843 =
                                            let uu____82846 =
                                              let uu____82847 =
                                                let uu____82855 =
                                                  let uu____82856 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____82857 =
                                                    let uu____82868 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____82868)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____82856 uu____82857
                                                   in
                                                (uu____82855,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____82847
                                               in
                                            [uu____82846]  in
                                          FStar_List.append karr uu____82843
                                           in
                                        FStar_All.pipe_right uu____82840
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____82837
                                   in
                                let aux =
                                  let uu____82887 =
                                    let uu____82890 =
                                      inversion_axioms tapp vars  in
                                    let uu____82893 =
                                      let uu____82896 =
                                        let uu____82899 =
                                          let uu____82900 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____82900 env2 tapp
                                            vars
                                           in
                                        [uu____82899]  in
                                      FStar_All.pipe_right uu____82896
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____82890 uu____82893
                                     in
                                  FStar_List.append kindingAx uu____82887  in
                                let g =
                                  let uu____82908 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____82908
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82916,uu____82917,uu____82918,uu____82919,uu____82920)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82928,t,uu____82930,n_tps,uu____82932) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____82943 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____82943 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82991 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82991 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____83015 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____83015 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____83035 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____83035 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83114 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83114,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83121 =
                                   let uu____83122 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83122, true)
                                    in
                                 let uu____83130 =
                                   let uu____83137 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83137
                                    in
                                 FStar_All.pipe_right uu____83121 uu____83130
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
                               let uu____83149 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____83149 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83161::uu____83162 ->
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
                                            let uu____83211 =
                                              let uu____83212 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83212]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83211
                                             in
                                          let uu____83238 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83239 =
                                            let uu____83250 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83250)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83238 uu____83239
                                      | uu____83277 -> tok_typing  in
                                    let uu____83288 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83288 with
                                     | (vars',guards',env'',decls_formals,uu____83313)
                                         ->
                                         let uu____83326 =
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
                                         (match uu____83326 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83356 ->
                                                    let uu____83365 =
                                                      let uu____83366 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83366
                                                       in
                                                    [uu____83365]
                                                 in
                                              let encode_elim uu____83382 =
                                                let uu____83383 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83383 with
                                                | (head1,args) ->
                                                    let uu____83434 =
                                                      let uu____83435 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83435.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83434 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83447;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83448;_},uu____83449)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83455 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83455
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
                                                                  | uu____83518
                                                                    ->
                                                                    let uu____83519
                                                                    =
                                                                    let uu____83525
                                                                    =
                                                                    let uu____83527
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83527
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83525)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83519
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83550
                                                                    =
                                                                    let uu____83552
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83552
                                                                     in
                                                                    if
                                                                    uu____83550
                                                                    then
                                                                    let uu____83574
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83574]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83577
                                                                =
                                                                let uu____83591
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83648
                                                                     ->
                                                                    fun
                                                                    uu____83649
                                                                     ->
                                                                    match 
                                                                    (uu____83648,
                                                                    uu____83649)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83760
                                                                    =
                                                                    let uu____83768
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83768
                                                                     in
                                                                    (match uu____83760
                                                                    with
                                                                    | 
                                                                    (uu____83782,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83793
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83793
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83798
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83798
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
                                                                  uu____83591
                                                                 in
                                                              (match uu____83577
                                                               with
                                                               | (uu____83819,arg_vars,elim_eqns_or_guards,uu____83822)
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
                                                                    let uu____83849
                                                                    =
                                                                    let uu____83857
                                                                    =
                                                                    let uu____83858
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83859
                                                                    =
                                                                    let uu____83870
                                                                    =
                                                                    let uu____83871
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83871
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83873
                                                                    =
                                                                    let uu____83874
                                                                    =
                                                                    let uu____83879
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83879)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83874
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83870,
                                                                    uu____83873)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83858
                                                                    uu____83859
                                                                     in
                                                                    (uu____83857,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83849
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83894
                                                                    =
                                                                    let uu____83895
                                                                    =
                                                                    let uu____83901
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83901,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83895
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83894
                                                                     in
                                                                    let uu____83904
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83904
                                                                    then
                                                                    let x =
                                                                    let uu____83908
                                                                    =
                                                                    let uu____83914
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83914,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83908
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83919
                                                                    =
                                                                    let uu____83927
                                                                    =
                                                                    let uu____83928
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83929
                                                                    =
                                                                    let uu____83940
                                                                    =
                                                                    let uu____83945
                                                                    =
                                                                    let uu____83948
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83948]
                                                                     in
                                                                    [uu____83945]
                                                                     in
                                                                    let uu____83953
                                                                    =
                                                                    let uu____83954
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83961
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83959,
                                                                    uu____83961)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83954
                                                                     in
                                                                    (uu____83940,
                                                                    [x],
                                                                    uu____83953)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83928
                                                                    uu____83929
                                                                     in
                                                                    let uu____83982
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83927,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83982)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83919
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83993
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
                                                                    (let uu____84016
                                                                    =
                                                                    let uu____84017
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84017
                                                                    dapp1  in
                                                                    [uu____84016])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83993
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84024
                                                                    =
                                                                    let uu____84032
                                                                    =
                                                                    let uu____84033
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84034
                                                                    =
                                                                    let uu____84045
                                                                    =
                                                                    let uu____84046
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84046
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84048
                                                                    =
                                                                    let uu____84049
                                                                    =
                                                                    let uu____84054
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84054)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84049
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84045,
                                                                    uu____84048)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84033
                                                                    uu____84034
                                                                     in
                                                                    (uu____84032,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84024)
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
                                                         let uu____84073 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84073
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
                                                                  | uu____84136
                                                                    ->
                                                                    let uu____84137
                                                                    =
                                                                    let uu____84143
                                                                    =
                                                                    let uu____84145
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84145
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84143)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84137
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84168
                                                                    =
                                                                    let uu____84170
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84170
                                                                     in
                                                                    if
                                                                    uu____84168
                                                                    then
                                                                    let uu____84192
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84192]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84195
                                                                =
                                                                let uu____84209
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84266
                                                                     ->
                                                                    fun
                                                                    uu____84267
                                                                     ->
                                                                    match 
                                                                    (uu____84266,
                                                                    uu____84267)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84378
                                                                    =
                                                                    let uu____84386
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84386
                                                                     in
                                                                    (match uu____84378
                                                                    with
                                                                    | 
                                                                    (uu____84400,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84411
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84411
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84416
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84416
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
                                                                  uu____84209
                                                                 in
                                                              (match uu____84195
                                                               with
                                                               | (uu____84437,arg_vars,elim_eqns_or_guards,uu____84440)
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
                                                                    let uu____84467
                                                                    =
                                                                    let uu____84475
                                                                    =
                                                                    let uu____84476
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84477
                                                                    =
                                                                    let uu____84488
                                                                    =
                                                                    let uu____84489
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84489
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84491
                                                                    =
                                                                    let uu____84492
                                                                    =
                                                                    let uu____84497
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84497)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84492
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84488,
                                                                    uu____84491)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84476
                                                                    uu____84477
                                                                     in
                                                                    (uu____84475,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84467
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84512
                                                                    =
                                                                    let uu____84513
                                                                    =
                                                                    let uu____84519
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84519,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84513
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84512
                                                                     in
                                                                    let uu____84522
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84522
                                                                    then
                                                                    let x =
                                                                    let uu____84526
                                                                    =
                                                                    let uu____84532
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84532,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84526
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84537
                                                                    =
                                                                    let uu____84545
                                                                    =
                                                                    let uu____84546
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84547
                                                                    =
                                                                    let uu____84558
                                                                    =
                                                                    let uu____84563
                                                                    =
                                                                    let uu____84566
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84566]
                                                                     in
                                                                    [uu____84563]
                                                                     in
                                                                    let uu____84571
                                                                    =
                                                                    let uu____84572
                                                                    =
                                                                    let uu____84577
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84577,
                                                                    uu____84579)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84572
                                                                     in
                                                                    (uu____84558,
                                                                    [x],
                                                                    uu____84571)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84546
                                                                    uu____84547
                                                                     in
                                                                    let uu____84600
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84545,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84600)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84537
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84611
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
                                                                    (let uu____84634
                                                                    =
                                                                    let uu____84635
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84635
                                                                    dapp1  in
                                                                    [uu____84634])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84611
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84642
                                                                    =
                                                                    let uu____84650
                                                                    =
                                                                    let uu____84651
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84652
                                                                    =
                                                                    let uu____84663
                                                                    =
                                                                    let uu____84664
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84664
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84666
                                                                    =
                                                                    let uu____84667
                                                                    =
                                                                    let uu____84672
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84672)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84667
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84663,
                                                                    uu____84666)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84651
                                                                    uu____84652
                                                                     in
                                                                    (uu____84650,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84642)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84689 ->
                                                         ((let uu____84691 =
                                                             let uu____84697
                                                               =
                                                               let uu____84699
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84701
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84699
                                                                 uu____84701
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84697)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84691);
                                                          ([], [])))
                                                 in
                                              let uu____84709 =
                                                encode_elim ()  in
                                              (match uu____84709 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84735 =
                                                       let uu____84738 =
                                                         let uu____84741 =
                                                           let uu____84744 =
                                                             let uu____84747
                                                               =
                                                               let uu____84750
                                                                 =
                                                                 let uu____84753
                                                                   =
                                                                   let uu____84754
                                                                    =
                                                                    let uu____84766
                                                                    =
                                                                    let uu____84767
                                                                    =
                                                                    let uu____84769
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84769
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84767
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84766)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84754
                                                                    in
                                                                 [uu____84753]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84750
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84747
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84780 =
                                                             let uu____84783
                                                               =
                                                               let uu____84786
                                                                 =
                                                                 let uu____84789
                                                                   =
                                                                   let uu____84792
                                                                    =
                                                                    let uu____84795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84800
                                                                    =
                                                                    let uu____84803
                                                                    =
                                                                    let uu____84804
                                                                    =
                                                                    let uu____84812
                                                                    =
                                                                    let uu____84813
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84814
                                                                    =
                                                                    let uu____84825
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84825)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84813
                                                                    uu____84814
                                                                     in
                                                                    (uu____84812,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84804
                                                                     in
                                                                    let uu____84838
                                                                    =
                                                                    let uu____84841
                                                                    =
                                                                    let uu____84842
                                                                    =
                                                                    let uu____84850
                                                                    =
                                                                    let uu____84851
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84852
                                                                    =
                                                                    let uu____84863
                                                                    =
                                                                    let uu____84864
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84864
                                                                    vars'  in
                                                                    let uu____84866
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84863,
                                                                    uu____84866)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84851
                                                                    uu____84852
                                                                     in
                                                                    (uu____84850,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84842
                                                                     in
                                                                    [uu____84841]
                                                                     in
                                                                    uu____84803
                                                                    ::
                                                                    uu____84838
                                                                     in
                                                                    uu____84795
                                                                    ::
                                                                    uu____84800
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84792
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84789
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84786
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84783
                                                              in
                                                           FStar_List.append
                                                             uu____84744
                                                             uu____84780
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84741
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84738
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84735
                                                      in
                                                   let uu____84883 =
                                                     let uu____84884 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84884 g
                                                      in
                                                   (uu____84883, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84918  ->
              fun se  ->
                match uu____84918 with
                | (g,env1) ->
                    let uu____84938 = encode_sigelt env1 se  in
                    (match uu____84938 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____85006 =
        match uu____85006 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____85043 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____85051 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____85051
                   then
                     let uu____85056 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____85058 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____85060 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____85056 uu____85058 uu____85060
                   else ());
                  (let uu____85065 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____85065 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____85083 =
                         let uu____85091 =
                           let uu____85093 =
                             let uu____85095 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85095
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85093  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85091
                          in
                       (match uu____85083 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85115 = FStar_Options.log_queries ()
                                 in
                              if uu____85115
                              then
                                let uu____85118 =
                                  let uu____85120 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85122 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85124 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85120 uu____85122 uu____85124
                                   in
                                FStar_Pervasives_Native.Some uu____85118
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85140 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85150 =
                                let uu____85153 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85153  in
                              FStar_List.append uu____85140 uu____85150  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85165,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85185 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85185 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85206 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85206 with | (uu____85233,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85286  ->
              match uu____85286 with
              | (l,uu____85295,uu____85296) ->
                  let uu____85299 =
                    let uu____85311 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85311, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85299))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85344  ->
              match uu____85344 with
              | (l,uu____85355,uu____85356) ->
                  let uu____85359 =
                    let uu____85360 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85363  -> FStar_SMTEncoding_Term.Echo _85363)
                      uu____85360
                     in
                  let uu____85364 =
                    let uu____85367 =
                      let uu____85368 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85368  in
                    [uu____85367]  in
                  uu____85359 :: uu____85364))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85386 =
      let uu____85389 =
        let uu____85390 = FStar_Util.psmap_empty ()  in
        let uu____85405 =
          let uu____85414 = FStar_Util.psmap_empty ()  in (uu____85414, [])
           in
        let uu____85421 =
          let uu____85423 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85423 FStar_Ident.string_of_lid  in
        let uu____85425 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85390;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85405;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85421;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85425
        }  in
      [uu____85389]  in
    FStar_ST.op_Colon_Equals last_env uu____85386
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85469 = FStar_ST.op_Bang last_env  in
      match uu____85469 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85497 ->
          let uu___2182_85500 = e  in
          let uu____85501 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2182_85500.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2182_85500.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2182_85500.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2182_85500.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2182_85500.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2182_85500.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2182_85500.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85501;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2182_85500.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2182_85500.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85509 = FStar_ST.op_Bang last_env  in
    match uu____85509 with
    | [] -> failwith "Empty env stack"
    | uu____85536::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85568  ->
    let uu____85569 = FStar_ST.op_Bang last_env  in
    match uu____85569 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85629  ->
    let uu____85630 = FStar_ST.op_Bang last_env  in
    match uu____85630 with
    | [] -> failwith "Popping an empty stack"
    | uu____85657::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85694  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85747  ->
         let uu____85748 = snapshot_env ()  in
         match uu____85748 with
         | (env_depth,()) ->
             let uu____85770 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85770 with
              | (varops_depth,()) ->
                  let uu____85792 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85792 with
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
        (fun uu____85850  ->
           let uu____85851 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85851 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85946 = snapshot msg  in () 
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
        | (uu____85992::uu____85993,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2243_86001 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2243_86001.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2243_86001.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2243_86001.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____86002 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2249_86029 = elt  in
        let uu____86030 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2249_86029.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2249_86029.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____86030;
          FStar_SMTEncoding_Term.a_names =
            (uu___2249_86029.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____86050 =
        let uu____86053 =
          let uu____86054 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____86054  in
        let uu____86055 = open_fact_db_tags env  in uu____86053 ::
          uu____86055
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____86050
  
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
      let uu____86082 = encode_sigelt env se  in
      match uu____86082 with
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
                (let uu____86128 =
                   let uu____86131 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86131
                    in
                 match uu____86128 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86146 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86146
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86176 = FStar_Options.log_queries ()  in
        if uu____86176
        then
          let uu____86181 =
            let uu____86182 =
              let uu____86184 =
                let uu____86186 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86186 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86184  in
            FStar_SMTEncoding_Term.Caption uu____86182  in
          uu____86181 :: decls
        else decls  in
      (let uu____86205 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86205
       then
         let uu____86208 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86208
       else ());
      (let env =
         let uu____86214 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86214 tcenv  in
       let uu____86215 = encode_top_level_facts env se  in
       match uu____86215 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86229 =
               let uu____86232 =
                 let uu____86235 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86235
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86232  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86229)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86268 = FStar_Options.log_queries ()  in
          if uu____86268
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2287_86288 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2287_86288.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2287_86288.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2287_86288.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2287_86288.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2287_86288.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2287_86288.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2287_86288.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2287_86288.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2287_86288.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2287_86288.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86293 =
             let uu____86296 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86296
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86293  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86316 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86316
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
          (let uu____86340 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86340
           then
             let uu____86343 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86343
           else ());
          (let env =
             let uu____86351 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86351
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86390  ->
                     fun se  ->
                       match uu____86390 with
                       | (g,env2) ->
                           let uu____86410 = encode_top_level_facts env2 se
                              in
                           (match uu____86410 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86433 =
             encode_signature
               (let uu___2310_86442 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2310_86442.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2310_86442.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2310_86442.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2310_86442.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2310_86442.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2310_86442.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2310_86442.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2310_86442.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2310_86442.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2310_86442.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86433 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86458 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86458
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86464 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86464))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86492  ->
        match uu____86492 with
        | (decls,fvbs) ->
            ((let uu____86506 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86506
              then ()
              else
                (let uu____86511 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86511
                 then
                   let uu____86514 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86514
                 else ()));
             (let env =
                let uu____86522 = get_env name tcenv  in
                FStar_All.pipe_right uu____86522
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86524 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86524
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86538 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86538
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
        (let uu____86600 =
           let uu____86602 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86602.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86600);
        (let env =
           let uu____86604 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86604 tcenv  in
         let uu____86605 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86644 = aux rest  in
                 (match uu____86644 with
                  | (out,rest1) ->
                      let t =
                        let uu____86672 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86672 with
                        | FStar_Pervasives_Native.Some uu____86675 ->
                            let uu____86676 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86676
                              x.FStar_Syntax_Syntax.sort
                        | uu____86677 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86681 =
                        let uu____86684 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2351_86687 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2351_86687.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2351_86687.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86684 :: out  in
                      (uu____86681, rest1))
             | uu____86692 -> ([], bindings)  in
           let uu____86699 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86699 with
           | (closing,bindings) ->
               let uu____86726 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86726, bindings)
            in
         match uu____86605 with
         | (q1,bindings) ->
             let uu____86757 = encode_env_bindings env bindings  in
             (match uu____86757 with
              | (env_decls,env1) ->
                  ((let uu____86779 =
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
                    if uu____86779
                    then
                      let uu____86786 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86786
                    else ());
                   (let uu____86791 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86791 with
                    | (phi,qdecls) ->
                        let uu____86812 =
                          let uu____86817 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86817 phi
                           in
                        (match uu____86812 with
                         | (labels,phi1) ->
                             let uu____86834 = encode_labels labels  in
                             (match uu____86834 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86870 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86870
                                    then
                                      let uu____86875 =
                                        let uu____86876 =
                                          let uu____86878 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86878
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86876
                                         in
                                      [uu____86875]
                                    else []  in
                                  let query_prelude =
                                    let uu____86886 =
                                      let uu____86887 =
                                        let uu____86888 =
                                          let uu____86891 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86898 =
                                            let uu____86901 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86901
                                             in
                                          FStar_List.append uu____86891
                                            uu____86898
                                           in
                                        FStar_List.append env_decls
                                          uu____86888
                                         in
                                      FStar_All.pipe_right uu____86887
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86886
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86911 =
                                      let uu____86919 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86920 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86919,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86920)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86911
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
  