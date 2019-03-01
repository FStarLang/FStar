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
  let uu____72848 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72848 with
  | (asym,a) ->
      let uu____72859 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72859 with
       | (xsym,x) ->
           let uu____72870 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72870 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72948 =
                      let uu____72960 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72960, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72948  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72980 =
                      let uu____72988 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72988)  in
                    FStar_SMTEncoding_Util.mkApp uu____72980  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____73007 =
                    let uu____73010 =
                      let uu____73013 =
                        let uu____73016 =
                          let uu____73017 =
                            let uu____73025 =
                              let uu____73026 =
                                let uu____73037 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____73037)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____73026
                               in
                            (uu____73025, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____73017  in
                        let uu____73049 =
                          let uu____73052 =
                            let uu____73053 =
                              let uu____73061 =
                                let uu____73062 =
                                  let uu____73073 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____73073)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____73062
                                 in
                              (uu____73061,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____73053  in
                          [uu____73052]  in
                        uu____73016 :: uu____73049  in
                      xtok_decl :: uu____73013  in
                    xname_decl :: uu____73010  in
                  (xtok1, (FStar_List.length vars), uu____73007)  in
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
                  let uu____73243 =
                    let uu____73264 =
                      let uu____73283 =
                        let uu____73284 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73284
                         in
                      quant axy uu____73283  in
                    (FStar_Parser_Const.op_Eq, uu____73264)  in
                  let uu____73301 =
                    let uu____73324 =
                      let uu____73345 =
                        let uu____73364 =
                          let uu____73365 =
                            let uu____73366 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73366  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73365
                           in
                        quant axy uu____73364  in
                      (FStar_Parser_Const.op_notEq, uu____73345)  in
                    let uu____73383 =
                      let uu____73406 =
                        let uu____73427 =
                          let uu____73446 =
                            let uu____73447 =
                              let uu____73448 =
                                let uu____73453 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73454 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73453, uu____73454)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73448  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73447
                             in
                          quant xy uu____73446  in
                        (FStar_Parser_Const.op_And, uu____73427)  in
                      let uu____73471 =
                        let uu____73494 =
                          let uu____73515 =
                            let uu____73534 =
                              let uu____73535 =
                                let uu____73536 =
                                  let uu____73541 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73542 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73541, uu____73542)  in
                                FStar_SMTEncoding_Util.mkOr uu____73536  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73535
                               in
                            quant xy uu____73534  in
                          (FStar_Parser_Const.op_Or, uu____73515)  in
                        let uu____73559 =
                          let uu____73582 =
                            let uu____73603 =
                              let uu____73622 =
                                let uu____73623 =
                                  let uu____73624 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73624
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73623
                                 in
                              quant qx uu____73622  in
                            (FStar_Parser_Const.op_Negation, uu____73603)  in
                          let uu____73641 =
                            let uu____73664 =
                              let uu____73685 =
                                let uu____73704 =
                                  let uu____73705 =
                                    let uu____73706 =
                                      let uu____73711 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73712 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73711, uu____73712)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73706
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73705
                                   in
                                quant xy uu____73704  in
                              (FStar_Parser_Const.op_LT, uu____73685)  in
                            let uu____73729 =
                              let uu____73752 =
                                let uu____73773 =
                                  let uu____73792 =
                                    let uu____73793 =
                                      let uu____73794 =
                                        let uu____73799 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73800 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73799, uu____73800)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73794
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73793
                                     in
                                  quant xy uu____73792  in
                                (FStar_Parser_Const.op_LTE, uu____73773)  in
                              let uu____73817 =
                                let uu____73840 =
                                  let uu____73861 =
                                    let uu____73880 =
                                      let uu____73881 =
                                        let uu____73882 =
                                          let uu____73887 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73888 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73887, uu____73888)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73882
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73881
                                       in
                                    quant xy uu____73880  in
                                  (FStar_Parser_Const.op_GT, uu____73861)  in
                                let uu____73905 =
                                  let uu____73928 =
                                    let uu____73949 =
                                      let uu____73968 =
                                        let uu____73969 =
                                          let uu____73970 =
                                            let uu____73975 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73976 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73975, uu____73976)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73970
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73969
                                         in
                                      quant xy uu____73968  in
                                    (FStar_Parser_Const.op_GTE, uu____73949)
                                     in
                                  let uu____73993 =
                                    let uu____74016 =
                                      let uu____74037 =
                                        let uu____74056 =
                                          let uu____74057 =
                                            let uu____74058 =
                                              let uu____74063 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____74064 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____74063, uu____74064)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____74058
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____74057
                                           in
                                        quant xy uu____74056  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____74037)
                                       in
                                    let uu____74081 =
                                      let uu____74104 =
                                        let uu____74125 =
                                          let uu____74144 =
                                            let uu____74145 =
                                              let uu____74146 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74146
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74145
                                             in
                                          quant qx uu____74144  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74125)
                                         in
                                      let uu____74163 =
                                        let uu____74186 =
                                          let uu____74207 =
                                            let uu____74226 =
                                              let uu____74227 =
                                                let uu____74228 =
                                                  let uu____74233 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74234 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74233, uu____74234)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74228
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74227
                                               in
                                            quant xy uu____74226  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74207)
                                           in
                                        let uu____74251 =
                                          let uu____74274 =
                                            let uu____74295 =
                                              let uu____74314 =
                                                let uu____74315 =
                                                  let uu____74316 =
                                                    let uu____74321 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74322 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74321,
                                                      uu____74322)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74316
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74315
                                                 in
                                              quant xy uu____74314  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74295)
                                             in
                                          let uu____74339 =
                                            let uu____74362 =
                                              let uu____74383 =
                                                let uu____74402 =
                                                  let uu____74403 =
                                                    let uu____74404 =
                                                      let uu____74409 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74410 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74409,
                                                        uu____74410)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74404
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74403
                                                   in
                                                quant xy uu____74402  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74383)
                                               in
                                            let uu____74427 =
                                              let uu____74450 =
                                                let uu____74471 =
                                                  let uu____74490 =
                                                    let uu____74491 =
                                                      let uu____74492 =
                                                        let uu____74497 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74498 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74497,
                                                          uu____74498)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74492
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74491
                                                     in
                                                  quant xy uu____74490  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74471)
                                                 in
                                              let uu____74515 =
                                                let uu____74538 =
                                                  let uu____74559 =
                                                    let uu____74578 =
                                                      let uu____74579 =
                                                        let uu____74580 =
                                                          let uu____74585 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74586 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74585,
                                                            uu____74586)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74580
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74579
                                                       in
                                                    quant xy uu____74578  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74559)
                                                   in
                                                let uu____74603 =
                                                  let uu____74626 =
                                                    let uu____74647 =
                                                      let uu____74666 =
                                                        let uu____74667 =
                                                          let uu____74668 =
                                                            let uu____74673 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74674 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74673,
                                                              uu____74674)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74668
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74667
                                                         in
                                                      quant xy uu____74666
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74647)
                                                     in
                                                  let uu____74691 =
                                                    let uu____74714 =
                                                      let uu____74735 =
                                                        let uu____74754 =
                                                          let uu____74755 =
                                                            let uu____74756 =
                                                              let uu____74761
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74762
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74761,
                                                                uu____74762)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74756
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74755
                                                           in
                                                        quant xy uu____74754
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74735)
                                                       in
                                                    let uu____74779 =
                                                      let uu____74802 =
                                                        let uu____74823 =
                                                          let uu____74842 =
                                                            let uu____74843 =
                                                              let uu____74844
                                                                =
                                                                let uu____74849
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74850
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74849,
                                                                  uu____74850)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74844
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74843
                                                             in
                                                          quant xy
                                                            uu____74842
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74823)
                                                         in
                                                      let uu____74867 =
                                                        let uu____74890 =
                                                          let uu____74911 =
                                                            let uu____74930 =
                                                              let uu____74931
                                                                =
                                                                let uu____74932
                                                                  =
                                                                  let uu____74937
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74938
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74937,
                                                                    uu____74938)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74932
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74931
                                                               in
                                                            quant xy
                                                              uu____74930
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74911)
                                                           in
                                                        let uu____74955 =
                                                          let uu____74978 =
                                                            let uu____74999 =
                                                              let uu____75018
                                                                =
                                                                let uu____75019
                                                                  =
                                                                  let uu____75020
                                                                    =
                                                                    let uu____75025
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75026
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75025,
                                                                    uu____75026)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____75020
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____75019
                                                                 in
                                                              quant xy
                                                                uu____75018
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74999)
                                                             in
                                                          let uu____75043 =
                                                            let uu____75066 =
                                                              let uu____75087
                                                                =
                                                                let uu____75106
                                                                  =
                                                                  let uu____75107
                                                                    =
                                                                    let uu____75108
                                                                    =
                                                                    let uu____75113
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75114
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75113,
                                                                    uu____75114)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75108
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75107
                                                                   in
                                                                quant xy
                                                                  uu____75106
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75087)
                                                               in
                                                            let uu____75131 =
                                                              let uu____75154
                                                                =
                                                                let uu____75175
                                                                  =
                                                                  let uu____75194
                                                                    =
                                                                    let uu____75195
                                                                    =
                                                                    let uu____75196
                                                                    =
                                                                    let uu____75201
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75202
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75201,
                                                                    uu____75202)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75196
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75195
                                                                     in
                                                                  quant xy
                                                                    uu____75194
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75175)
                                                                 in
                                                              let uu____75219
                                                                =
                                                                let uu____75242
                                                                  =
                                                                  let uu____75263
                                                                    =
                                                                    let uu____75282
                                                                    =
                                                                    let uu____75283
                                                                    =
                                                                    let uu____75284
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75284
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75283
                                                                     in
                                                                    quant qx
                                                                    uu____75282
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75263)
                                                                   in
                                                                [uu____75242]
                                                                 in
                                                              uu____75154 ::
                                                                uu____75219
                                                               in
                                                            uu____75066 ::
                                                              uu____75131
                                                             in
                                                          uu____74978 ::
                                                            uu____75043
                                                           in
                                                        uu____74890 ::
                                                          uu____74955
                                                         in
                                                      uu____74802 ::
                                                        uu____74867
                                                       in
                                                    uu____74714 ::
                                                      uu____74779
                                                     in
                                                  uu____74626 :: uu____74691
                                                   in
                                                uu____74538 :: uu____74603
                                                 in
                                              uu____74450 :: uu____74515  in
                                            uu____74362 :: uu____74427  in
                                          uu____74274 :: uu____74339  in
                                        uu____74186 :: uu____74251  in
                                      uu____74104 :: uu____74163  in
                                    uu____74016 :: uu____74081  in
                                  uu____73928 :: uu____73993  in
                                uu____73840 :: uu____73905  in
                              uu____73752 :: uu____73817  in
                            uu____73664 :: uu____73729  in
                          uu____73582 :: uu____73641  in
                        uu____73494 :: uu____73559  in
                      uu____73406 :: uu____73471  in
                    uu____73324 :: uu____73383  in
                  uu____73243 :: uu____73301  in
                let mk1 l v1 =
                  let uu____75823 =
                    let uu____75835 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75925  ->
                              match uu____75925 with
                              | (l',uu____75946) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75835
                      (FStar_Option.map
                         (fun uu____76045  ->
                            match uu____76045 with
                            | (uu____76073,b) ->
                                let uu____76107 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76107 v1))
                     in
                  FStar_All.pipe_right uu____75823 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76190  ->
                          match uu____76190 with
                          | (l',uu____76211) -> FStar_Ident.lid_equals l l'))
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
          let uu____76285 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76285 with
          | (xxsym,xx) ->
              let uu____76296 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76296 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76312 =
                     let uu____76320 =
                       let uu____76321 =
                         let uu____76332 =
                           let uu____76333 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76343 =
                             let uu____76354 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76354 :: vars  in
                           uu____76333 :: uu____76343  in
                         let uu____76380 =
                           let uu____76381 =
                             let uu____76386 =
                               let uu____76387 =
                                 let uu____76392 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76392)  in
                               FStar_SMTEncoding_Util.mkEq uu____76387  in
                             (xx_has_type, uu____76386)  in
                           FStar_SMTEncoding_Util.mkImp uu____76381  in
                         ([[xx_has_type]], uu____76332, uu____76380)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76321  in
                     let uu____76405 =
                       let uu____76407 =
                         let uu____76409 =
                           let uu____76411 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76411  in
                         Prims.op_Hat module_name uu____76409  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76407
                        in
                     (uu____76320,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76405)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76312)
  
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
    let uu____76467 =
      let uu____76469 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76469  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76467  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76491 =
      let uu____76492 =
        let uu____76500 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76500, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76492  in
    let uu____76505 =
      let uu____76508 =
        let uu____76509 =
          let uu____76517 =
            let uu____76518 =
              let uu____76529 =
                let uu____76530 =
                  let uu____76535 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76535)  in
                FStar_SMTEncoding_Util.mkImp uu____76530  in
              ([[typing_pred]], [xx], uu____76529)  in
            let uu____76560 =
              let uu____76575 = FStar_TypeChecker_Env.get_range env  in
              let uu____76576 = mkForall_fuel1 env  in
              uu____76576 uu____76575  in
            uu____76560 uu____76518  in
          (uu____76517, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76509  in
      [uu____76508]  in
    uu____76491 :: uu____76505  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76623 =
      let uu____76624 =
        let uu____76632 =
          let uu____76633 = FStar_TypeChecker_Env.get_range env  in
          let uu____76634 =
            let uu____76645 =
              let uu____76650 =
                let uu____76653 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76653]  in
              [uu____76650]  in
            let uu____76658 =
              let uu____76659 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76659 tt  in
            (uu____76645, [bb], uu____76658)  in
          FStar_SMTEncoding_Term.mkForall uu____76633 uu____76634  in
        (uu____76632, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76624  in
    let uu____76684 =
      let uu____76687 =
        let uu____76688 =
          let uu____76696 =
            let uu____76697 =
              let uu____76708 =
                let uu____76709 =
                  let uu____76714 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76714)  in
                FStar_SMTEncoding_Util.mkImp uu____76709  in
              ([[typing_pred]], [xx], uu____76708)  in
            let uu____76741 =
              let uu____76756 = FStar_TypeChecker_Env.get_range env  in
              let uu____76757 = mkForall_fuel1 env  in
              uu____76757 uu____76756  in
            uu____76741 uu____76697  in
          (uu____76696, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76688  in
      [uu____76687]  in
    uu____76623 :: uu____76684  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76800 =
        let uu____76801 =
          let uu____76807 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76807, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76801  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76800  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76821 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76821  in
    let uu____76826 =
      let uu____76827 =
        let uu____76835 =
          let uu____76836 = FStar_TypeChecker_Env.get_range env  in
          let uu____76837 =
            let uu____76848 =
              let uu____76853 =
                let uu____76856 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76856]  in
              [uu____76853]  in
            let uu____76861 =
              let uu____76862 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76862 tt  in
            (uu____76848, [bb], uu____76861)  in
          FStar_SMTEncoding_Term.mkForall uu____76836 uu____76837  in
        (uu____76835, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76827  in
    let uu____76887 =
      let uu____76890 =
        let uu____76891 =
          let uu____76899 =
            let uu____76900 =
              let uu____76911 =
                let uu____76912 =
                  let uu____76917 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76917)  in
                FStar_SMTEncoding_Util.mkImp uu____76912  in
              ([[typing_pred]], [xx], uu____76911)  in
            let uu____76944 =
              let uu____76959 = FStar_TypeChecker_Env.get_range env  in
              let uu____76960 = mkForall_fuel1 env  in
              uu____76960 uu____76959  in
            uu____76944 uu____76900  in
          (uu____76899, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76891  in
      let uu____76982 =
        let uu____76985 =
          let uu____76986 =
            let uu____76994 =
              let uu____76995 =
                let uu____77006 =
                  let uu____77007 =
                    let uu____77012 =
                      let uu____77013 =
                        let uu____77016 =
                          let uu____77019 =
                            let uu____77022 =
                              let uu____77023 =
                                let uu____77028 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____77029 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____77028, uu____77029)  in
                              FStar_SMTEncoding_Util.mkGT uu____77023  in
                            let uu____77031 =
                              let uu____77034 =
                                let uu____77035 =
                                  let uu____77040 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____77041 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____77040, uu____77041)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77035  in
                              let uu____77043 =
                                let uu____77046 =
                                  let uu____77047 =
                                    let uu____77052 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____77053 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____77052, uu____77053)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77047  in
                                [uu____77046]  in
                              uu____77034 :: uu____77043  in
                            uu____77022 :: uu____77031  in
                          typing_pred_y :: uu____77019  in
                        typing_pred :: uu____77016  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77013  in
                    (uu____77012, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77007  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77006)
                 in
              let uu____77086 =
                let uu____77101 = FStar_TypeChecker_Env.get_range env  in
                let uu____77102 = mkForall_fuel1 env  in
                uu____77102 uu____77101  in
              uu____77086 uu____76995  in
            (uu____76994,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76986  in
        [uu____76985]  in
      uu____76890 :: uu____76982  in
    uu____76826 :: uu____76887  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77145 =
        let uu____77146 =
          let uu____77152 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77152, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77146  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77145  in
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
      let uu____77168 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77168  in
    let uu____77173 =
      let uu____77174 =
        let uu____77182 =
          let uu____77183 = FStar_TypeChecker_Env.get_range env  in
          let uu____77184 =
            let uu____77195 =
              let uu____77200 =
                let uu____77203 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77203]  in
              [uu____77200]  in
            let uu____77208 =
              let uu____77209 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77209 tt  in
            (uu____77195, [bb], uu____77208)  in
          FStar_SMTEncoding_Term.mkForall uu____77183 uu____77184  in
        (uu____77182, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77174  in
    let uu____77234 =
      let uu____77237 =
        let uu____77238 =
          let uu____77246 =
            let uu____77247 =
              let uu____77258 =
                let uu____77259 =
                  let uu____77264 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77264)  in
                FStar_SMTEncoding_Util.mkImp uu____77259  in
              ([[typing_pred]], [xx], uu____77258)  in
            let uu____77291 =
              let uu____77306 = FStar_TypeChecker_Env.get_range env  in
              let uu____77307 = mkForall_fuel1 env  in
              uu____77307 uu____77306  in
            uu____77291 uu____77247  in
          (uu____77246, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77238  in
      let uu____77329 =
        let uu____77332 =
          let uu____77333 =
            let uu____77341 =
              let uu____77342 =
                let uu____77353 =
                  let uu____77354 =
                    let uu____77359 =
                      let uu____77360 =
                        let uu____77363 =
                          let uu____77366 =
                            let uu____77369 =
                              let uu____77370 =
                                let uu____77375 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77376 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77375, uu____77376)  in
                              FStar_SMTEncoding_Util.mkGT uu____77370  in
                            let uu____77378 =
                              let uu____77381 =
                                let uu____77382 =
                                  let uu____77387 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77388 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77387, uu____77388)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77382  in
                              let uu____77390 =
                                let uu____77393 =
                                  let uu____77394 =
                                    let uu____77399 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77400 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77399, uu____77400)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77394  in
                                [uu____77393]  in
                              uu____77381 :: uu____77390  in
                            uu____77369 :: uu____77378  in
                          typing_pred_y :: uu____77366  in
                        typing_pred :: uu____77363  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77360  in
                    (uu____77359, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77354  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77353)
                 in
              let uu____77433 =
                let uu____77448 = FStar_TypeChecker_Env.get_range env  in
                let uu____77449 = mkForall_fuel1 env  in
                uu____77449 uu____77448  in
              uu____77433 uu____77342  in
            (uu____77341,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77333  in
        [uu____77332]  in
      uu____77237 :: uu____77329  in
    uu____77173 :: uu____77234  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77496 =
      let uu____77497 =
        let uu____77505 =
          let uu____77506 = FStar_TypeChecker_Env.get_range env  in
          let uu____77507 =
            let uu____77518 =
              let uu____77523 =
                let uu____77526 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77526]  in
              [uu____77523]  in
            let uu____77531 =
              let uu____77532 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77532 tt  in
            (uu____77518, [bb], uu____77531)  in
          FStar_SMTEncoding_Term.mkForall uu____77506 uu____77507  in
        (uu____77505, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77497  in
    let uu____77557 =
      let uu____77560 =
        let uu____77561 =
          let uu____77569 =
            let uu____77570 =
              let uu____77581 =
                let uu____77582 =
                  let uu____77587 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77587)  in
                FStar_SMTEncoding_Util.mkImp uu____77582  in
              ([[typing_pred]], [xx], uu____77581)  in
            let uu____77614 =
              let uu____77629 = FStar_TypeChecker_Env.get_range env  in
              let uu____77630 = mkForall_fuel1 env  in
              uu____77630 uu____77629  in
            uu____77614 uu____77570  in
          (uu____77569, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77561  in
      [uu____77560]  in
    uu____77496 :: uu____77557  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77677 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77677]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77707 =
      let uu____77708 =
        let uu____77716 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77716, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77708  in
    [uu____77707]  in
  let mk_and_interp env conj uu____77739 =
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
    let uu____77768 =
      let uu____77769 =
        let uu____77777 =
          let uu____77778 = FStar_TypeChecker_Env.get_range env  in
          let uu____77779 =
            let uu____77790 =
              let uu____77791 =
                let uu____77796 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77796, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77791  in
            ([[l_and_a_b]], [aa; bb], uu____77790)  in
          FStar_SMTEncoding_Term.mkForall uu____77778 uu____77779  in
        (uu____77777, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77769  in
    [uu____77768]  in
  let mk_or_interp env disj uu____77851 =
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
    let uu____77880 =
      let uu____77881 =
        let uu____77889 =
          let uu____77890 = FStar_TypeChecker_Env.get_range env  in
          let uu____77891 =
            let uu____77902 =
              let uu____77903 =
                let uu____77908 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77908, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77903  in
            ([[l_or_a_b]], [aa; bb], uu____77902)  in
          FStar_SMTEncoding_Term.mkForall uu____77890 uu____77891  in
        (uu____77889, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77881  in
    [uu____77880]  in
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
    let uu____77986 =
      let uu____77987 =
        let uu____77995 =
          let uu____77996 = FStar_TypeChecker_Env.get_range env  in
          let uu____77997 =
            let uu____78008 =
              let uu____78009 =
                let uu____78014 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78014, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78009  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____78008)  in
          FStar_SMTEncoding_Term.mkForall uu____77996 uu____77997  in
        (uu____77995, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77987  in
    [uu____77986]  in
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
    let uu____78104 =
      let uu____78105 =
        let uu____78113 =
          let uu____78114 = FStar_TypeChecker_Env.get_range env  in
          let uu____78115 =
            let uu____78126 =
              let uu____78127 =
                let uu____78132 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78132, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78127  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78126)  in
          FStar_SMTEncoding_Term.mkForall uu____78114 uu____78115  in
        (uu____78113, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78105  in
    [uu____78104]  in
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
    let uu____78232 =
      let uu____78233 =
        let uu____78241 =
          let uu____78242 = FStar_TypeChecker_Env.get_range env  in
          let uu____78243 =
            let uu____78254 =
              let uu____78255 =
                let uu____78260 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78260, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78255  in
            ([[l_imp_a_b]], [aa; bb], uu____78254)  in
          FStar_SMTEncoding_Term.mkForall uu____78242 uu____78243  in
        (uu____78241, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78233  in
    [uu____78232]  in
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
    let uu____78344 =
      let uu____78345 =
        let uu____78353 =
          let uu____78354 = FStar_TypeChecker_Env.get_range env  in
          let uu____78355 =
            let uu____78366 =
              let uu____78367 =
                let uu____78372 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78372, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78367  in
            ([[l_iff_a_b]], [aa; bb], uu____78366)  in
          FStar_SMTEncoding_Term.mkForall uu____78354 uu____78355  in
        (uu____78353, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78345  in
    [uu____78344]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78443 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78443  in
    let uu____78448 =
      let uu____78449 =
        let uu____78457 =
          let uu____78458 = FStar_TypeChecker_Env.get_range env  in
          let uu____78459 =
            let uu____78470 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78470)  in
          FStar_SMTEncoding_Term.mkForall uu____78458 uu____78459  in
        (uu____78457, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78449  in
    [uu____78448]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78523 =
      let uu____78524 =
        let uu____78532 =
          let uu____78533 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78533 range_ty  in
        let uu____78534 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78532, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78534)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78524  in
    [uu____78523]  in
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
        let uu____78580 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78580 x1 t  in
      let uu____78582 = FStar_TypeChecker_Env.get_range env  in
      let uu____78583 =
        let uu____78594 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78594)  in
      FStar_SMTEncoding_Term.mkForall uu____78582 uu____78583  in
    let uu____78619 =
      let uu____78620 =
        let uu____78628 =
          let uu____78629 = FStar_TypeChecker_Env.get_range env  in
          let uu____78630 =
            let uu____78641 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78641)  in
          FStar_SMTEncoding_Term.mkForall uu____78629 uu____78630  in
        (uu____78628,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78620  in
    [uu____78619]  in
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
    let uu____78702 =
      let uu____78703 =
        let uu____78711 =
          let uu____78712 = FStar_TypeChecker_Env.get_range env  in
          let uu____78713 =
            let uu____78729 =
              let uu____78730 =
                let uu____78735 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78736 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78735, uu____78736)  in
              FStar_SMTEncoding_Util.mkAnd uu____78730  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78729)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78712 uu____78713  in
        (uu____78711,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78703  in
    [uu____78702]  in
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
          let uu____79294 =
            FStar_Util.find_opt
              (fun uu____79332  ->
                 match uu____79332 with
                 | (l,uu____79348) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79294 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79391,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79452 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79452 with
        | (form,decls) ->
            let uu____79461 =
              let uu____79464 =
                let uu____79467 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79467]  in
              FStar_All.pipe_right uu____79464
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79461
  
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
              let uu____79526 =
                ((let uu____79530 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79530) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79526
              then
                let arg_sorts =
                  let uu____79542 =
                    let uu____79543 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79543.FStar_Syntax_Syntax.n  in
                  match uu____79542 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79549) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79587  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79594 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79596 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79596 with
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
                    let uu____79632 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79632, env1)
              else
                (let uu____79637 = prims.is lid  in
                 if uu____79637
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79646 = prims.mk lid vname  in
                   match uu____79646 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79670 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79670, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79679 =
                      let uu____79698 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79698 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79726 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79726
                            then
                              let uu____79731 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79734 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79734.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79734.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79734.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79734.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79734.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79734.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79734.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79734.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79734.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79734.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79734.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79734.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79734.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79734.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79734.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79734.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79734.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79734.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79734.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79734.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79734.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79734.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79734.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79734.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79734.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79734.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79734.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79734.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79734.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79734.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79734.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79734.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79734.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79734.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79734.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79734.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79734.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79734.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79734.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79734.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79734.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79734.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79731
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79757 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79757)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79679 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79863  ->
                                  match uu___639_79863 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79867 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79867 with
                                       | (uu____79900,xxv) ->
                                           let xx =
                                             let uu____79939 =
                                               let uu____79940 =
                                                 let uu____79946 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79946,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79940
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79939
                                              in
                                           let uu____79949 =
                                             let uu____79950 =
                                               let uu____79958 =
                                                 let uu____79959 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79960 =
                                                   let uu____79971 =
                                                     let uu____79972 =
                                                       let uu____79977 =
                                                         let uu____79978 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79978
                                                          in
                                                       (vapp, uu____79977)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79972
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79971)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79959 uu____79960
                                                  in
                                               (uu____79958,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79950
                                              in
                                           [uu____79949])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79993 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79993 with
                                       | (uu____80026,xxv) ->
                                           let xx =
                                             let uu____80065 =
                                               let uu____80066 =
                                                 let uu____80072 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____80072,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____80066
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____80065
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
                                           let uu____80083 =
                                             let uu____80084 =
                                               let uu____80092 =
                                                 let uu____80093 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80094 =
                                                   let uu____80105 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80105)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80093 uu____80094
                                                  in
                                               (uu____80092,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80084
                                              in
                                           [uu____80083])
                                  | uu____80118 -> []))
                           in
                        let uu____80119 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80119 with
                         | (vars,guards,env',decls1,uu____80144) ->
                             let uu____80157 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80170 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80170, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80174 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80174 with
                                    | (g,ds) ->
                                        let uu____80187 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80187,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80157 with
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
                                  let should_thunk uu____80210 =
                                    let is_type1 t =
                                      let uu____80218 =
                                        let uu____80219 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80219.FStar_Syntax_Syntax.n  in
                                      match uu____80218 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80223 -> true
                                      | uu____80225 -> false  in
                                    let is_squash1 t =
                                      let uu____80234 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80234 with
                                      | (head1,uu____80253) ->
                                          let uu____80278 =
                                            let uu____80279 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80279.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80278 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80284;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80285;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80287;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80288;_};_},uu____80289)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80297 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80302 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80302))
                                       &&
                                       (let uu____80308 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80308))
                                      &&
                                      (let uu____80311 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80311)
                                     in
                                  let uu____80313 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80372 -> (false, vars)  in
                                  (match uu____80313 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80422 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80422 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80458 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80467 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80467
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80478 ->
                                                  let uu____80487 =
                                                    let uu____80495 =
                                                      get_vtok ()  in
                                                    (uu____80495, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80487
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80502 =
                                                let uu____80510 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80510)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80502
                                               in
                                            let uu____80524 =
                                              let vname_decl =
                                                let uu____80532 =
                                                  let uu____80544 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80544,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80532
                                                 in
                                              let uu____80555 =
                                                let env2 =
                                                  let uu___1026_80561 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80561.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80562 =
                                                  let uu____80564 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80564
                                                   in
                                                if uu____80562
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80555 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80581 =
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
                                                        let uu____80607 =
                                                          let uu____80610 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80610
                                                           in
                                                        let uu____80617 =
                                                          let uu____80618 =
                                                            let uu____80621 =
                                                              let uu____80622
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80622
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80626  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80626)
                                                              uu____80621
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80618
                                                           in
                                                        (uu____80607,
                                                          uu____80617)
                                                    | uu____80633 when
                                                        thunked ->
                                                        let uu____80644 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80644
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80659
                                                                 =
                                                                 let uu____80667
                                                                   =
                                                                   let uu____80670
                                                                    =
                                                                    let uu____80673
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80673]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80670
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80667)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80659
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80681
                                                               =
                                                               let uu____80689
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80689,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80681
                                                              in
                                                           let uu____80694 =
                                                             let uu____80697
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80697
                                                              in
                                                           (uu____80694,
                                                             env1))
                                                    | uu____80706 ->
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
                                                          let uu____80730 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80731 =
                                                            let uu____80742 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80742)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80730
                                                            uu____80731
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80752 =
                                                            let uu____80760 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80760,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80752
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
                                                            let uu____80771 =
                                                              let uu____80772
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80772]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80771
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80799 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80800 =
                                                              let uu____80811
                                                                =
                                                                let uu____80812
                                                                  =
                                                                  let uu____80817
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80818
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80817,
                                                                    uu____80818)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80812
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80811)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80799
                                                              uu____80800
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80847 =
                                                          let uu____80850 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80850
                                                           in
                                                        (uu____80847, env1)
                                                     in
                                                  (match uu____80581 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80871 =
                                                         let uu____80874 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80874
                                                           tok_decl
                                                          in
                                                       (uu____80871, env2))
                                               in
                                            (match uu____80524 with
                                             | (decls2,env2) ->
                                                 let uu____80893 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80903 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80903 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80918 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80918, decls)
                                                    in
                                                 (match uu____80893 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80933 =
                                                          let uu____80941 =
                                                            let uu____80942 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80943 =
                                                              let uu____80954
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80954)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80942
                                                              uu____80943
                                                             in
                                                          (uu____80941,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80933
                                                         in
                                                      let freshness =
                                                        let uu____80970 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80970
                                                        then
                                                          let uu____80978 =
                                                            let uu____80979 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80980 =
                                                              let uu____80993
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____81000
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80993,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____81000)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80979
                                                              uu____80980
                                                             in
                                                          let uu____81006 =
                                                            let uu____81009 =
                                                              let uu____81010
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____81010
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____81009]  in
                                                          uu____80978 ::
                                                            uu____81006
                                                        else []  in
                                                      let g =
                                                        let uu____81016 =
                                                          let uu____81019 =
                                                            let uu____81022 =
                                                              let uu____81025
                                                                =
                                                                let uu____81028
                                                                  =
                                                                  let uu____81031
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____81031
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____81028
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____81025
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____81022
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____81019
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____81016
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
          let uu____81071 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____81071 with
          | FStar_Pervasives_Native.None  ->
              let uu____81082 = encode_free_var false env x t t_norm []  in
              (match uu____81082 with
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
            let uu____81145 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81145 with
            | (decls,env1) ->
                let uu____81156 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81156
                then
                  let uu____81163 =
                    let uu____81164 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81164  in
                  (uu____81163, env1)
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
             (fun uu____81220  ->
                fun lb  ->
                  match uu____81220 with
                  | (decls,env1) ->
                      let uu____81240 =
                        let uu____81245 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81245
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81240 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81274 = FStar_Syntax_Util.head_and_args t  in
    match uu____81274 with
    | (hd1,args) ->
        let uu____81318 =
          let uu____81319 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81319.FStar_Syntax_Syntax.n  in
        (match uu____81318 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81325,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81349 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81360 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81368 = en  in
    let uu____81369 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81368.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81368.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81368.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81368.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81368.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81368.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81368.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81368.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81368.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81368.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81369
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81399  ->
      fun quals  ->
        match uu____81399 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81504 = FStar_Util.first_N nbinders formals  in
              match uu____81504 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81605  ->
                         fun uu____81606  ->
                           match (uu____81605, uu____81606) with
                           | ((formal,uu____81632),(binder,uu____81634)) ->
                               let uu____81655 =
                                 let uu____81662 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81662)  in
                               FStar_Syntax_Syntax.NT uu____81655) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81676 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81717  ->
                              match uu____81717 with
                              | (x,i) ->
                                  let uu____81736 =
                                    let uu___1139_81737 = x  in
                                    let uu____81738 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81737.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81737.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81738
                                    }  in
                                  (uu____81736, i)))
                       in
                    FStar_All.pipe_right uu____81676
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81762 =
                      let uu____81767 = FStar_Syntax_Subst.compress body  in
                      let uu____81768 =
                        let uu____81769 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81769
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81767
                        uu____81768
                       in
                    uu____81762 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81820 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81820.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81820.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81820.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81820.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81820.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81820.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81820.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81820.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81820.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81820.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81820.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81820.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81820.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81820.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81820.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81820.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81820.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81820.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81820.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81820.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81820.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81820.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81820.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81820.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81820.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81820.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81820.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81820.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81820.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81820.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81820.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81820.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81820.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81820.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81820.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81820.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81820.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81820.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81820.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81820.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81820.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81820.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81892  ->
                       fun uu____81893  ->
                         match (uu____81892, uu____81893) with
                         | ((x,uu____81919),(b,uu____81921)) ->
                             let uu____81942 =
                               let uu____81949 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81949)  in
                             FStar_Syntax_Syntax.NT uu____81942) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81974 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81974
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____82003 ->
                    let uu____82010 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____82010
                | uu____82011 when Prims.op_Negation norm1 ->
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
                | uu____82014 ->
                    let uu____82015 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____82015)
                 in
              let aux t1 e1 =
                let uu____82057 = FStar_Syntax_Util.abs_formals e1  in
                match uu____82057 with
                | (binders,body,lopt) ->
                    let uu____82089 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82105 -> arrow_formals_comp_norm false t1  in
                    (match uu____82089 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82139 =
                           if nformals < nbinders
                           then
                             let uu____82183 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82183 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82267 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82267)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82307 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82307 with
                                | (binders1,body1) ->
                                    let uu____82360 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82360))
                             else
                               (let uu____82373 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82373))
                            in
                         (match uu____82139 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82433 = aux t e  in
              match uu____82433 with
              | (binders,body,comp) ->
                  let uu____82479 =
                    let uu____82490 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82490
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82505 = aux comp1 body1  in
                      match uu____82505 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82479 with
                   | (binders1,body1,comp1) ->
                       let uu____82588 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82588, comp1))
               in
            (try
               (fun uu___1216_82615  ->
                  match () with
                  | () ->
                      let uu____82622 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82622
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82638 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82701  ->
                                   fun lb  ->
                                     match uu____82701 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82756 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82756
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82762 =
                                             let uu____82771 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82771
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82762 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82638 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82912;
                                    FStar_Syntax_Syntax.lbeff = uu____82913;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82915;
                                    FStar_Syntax_Syntax.lbpos = uu____82916;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82940 =
                                     let uu____82947 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82947 with
                                     | (tcenv',uu____82963,e_t) ->
                                         let uu____82969 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82980 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82969 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82997 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82997.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82940 with
                                    | (env',e1,t_norm1) ->
                                        let uu____83007 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____83007 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____83027 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____83027
                                               then
                                                 let uu____83032 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____83035 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____83032 uu____83035
                                               else ());
                                              (let uu____83040 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____83040 with
                                               | (vars,_guards,env'1,binder_decls,uu____83067)
                                                   ->
                                                   let uu____83080 =
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
                                                         let uu____83097 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83097
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83119 =
                                                          let uu____83120 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83121 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83120 fvb
                                                            uu____83121
                                                           in
                                                        (vars, uu____83119))
                                                      in
                                                   (match uu____83080 with
                                                    | (vars1,app) ->
                                                        let uu____83132 =
                                                          let is_logical =
                                                            let uu____83145 =
                                                              let uu____83146
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83146.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83145
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83152 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83156 =
                                                              let uu____83157
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83157
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83156
                                                              (fun lid  ->
                                                                 let uu____83166
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83166
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83167 =
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
                                                          if uu____83167
                                                          then
                                                            let uu____83183 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83184 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83183,
                                                              uu____83184)
                                                          else
                                                            (let uu____83195
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83195))
                                                           in
                                                        (match uu____83132
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83219
                                                                 =
                                                                 let uu____83227
                                                                   =
                                                                   let uu____83228
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83229
                                                                    =
                                                                    let uu____83240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83240)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83228
                                                                    uu____83229
                                                                    in
                                                                 let uu____83249
                                                                   =
                                                                   let uu____83250
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83250
                                                                    in
                                                                 (uu____83227,
                                                                   uu____83249,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83219
                                                                in
                                                             let uu____83256
                                                               =
                                                               let uu____83259
                                                                 =
                                                                 let uu____83262
                                                                   =
                                                                   let uu____83265
                                                                    =
                                                                    let uu____83268
                                                                    =
                                                                    let uu____83271
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83271
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83268
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83265
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83262
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83259
                                                                in
                                                             (uu____83256,
                                                               env2)))))))
                               | uu____83280 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83340 =
                                   let uu____83346 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83346,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83340  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83352 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83405  ->
                                         fun fvb  ->
                                           match uu____83405 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83460 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83460
                                                  in
                                               let gtok =
                                                 let uu____83464 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83464
                                                  in
                                               let env4 =
                                                 let uu____83467 =
                                                   let uu____83470 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83476  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83476) uu____83470
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83467
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83352 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83596
                                     t_norm uu____83598 =
                                     match (uu____83596, uu____83598) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83628;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83629;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83631;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83632;_})
                                         ->
                                         let uu____83659 =
                                           let uu____83666 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83666 with
                                           | (tcenv',uu____83682,e_t) ->
                                               let uu____83688 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83699 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83688 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83716 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83716.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83659 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83729 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83729
                                                then
                                                  let uu____83734 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83736 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83738 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83734 uu____83736
                                                    uu____83738
                                                else ());
                                               (let uu____83743 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83743 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83770 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83770 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83792 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83792
                                                           then
                                                             let uu____83797
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83799
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83802
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83804
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83797
                                                               uu____83799
                                                               uu____83802
                                                               uu____83804
                                                           else ());
                                                          (let uu____83809 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83809
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83838)
                                                               ->
                                                               let uu____83851
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83864
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83864,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83868
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83868
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83881
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83881,
                                                                    decls0))
                                                                  in
                                                               (match uu____83851
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
                                                                    let uu____83902
                                                                    =
                                                                    let uu____83914
                                                                    =
                                                                    let uu____83917
                                                                    =
                                                                    let uu____83920
                                                                    =
                                                                    let uu____83923
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83923
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83920
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83917
                                                                     in
                                                                    (g,
                                                                    uu____83914,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83902
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
                                                                    let uu____83953
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83953
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
                                                                    let uu____83968
                                                                    =
                                                                    let uu____83971
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83971
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83968
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83977
                                                                    =
                                                                    let uu____83980
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83980
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83977
                                                                     in
                                                                    let uu____83985
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83985
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____84001
                                                                    =
                                                                    let uu____84009
                                                                    =
                                                                    let uu____84010
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84011
                                                                    =
                                                                    let uu____84027
                                                                    =
                                                                    let uu____84028
                                                                    =
                                                                    let uu____84033
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____84033)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84028
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84027)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____84010
                                                                    uu____84011
                                                                     in
                                                                    let uu____84047
                                                                    =
                                                                    let uu____84048
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84048
                                                                     in
                                                                    (uu____84009,
                                                                    uu____84047,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84001
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____84055
                                                                    =
                                                                    let uu____84063
                                                                    =
                                                                    let uu____84064
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84065
                                                                    =
                                                                    let uu____84076
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84076)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84064
                                                                    uu____84065
                                                                     in
                                                                    (uu____84063,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84055
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84090
                                                                    =
                                                                    let uu____84098
                                                                    =
                                                                    let uu____84099
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84100
                                                                    =
                                                                    let uu____84111
                                                                    =
                                                                    let uu____84112
                                                                    =
                                                                    let uu____84117
                                                                    =
                                                                    let uu____84118
                                                                    =
                                                                    let uu____84121
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84121
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84118
                                                                     in
                                                                    (gsapp,
                                                                    uu____84117)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84112
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84111)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84099
                                                                    uu____84100
                                                                     in
                                                                    (uu____84098,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84090
                                                                     in
                                                                    let uu____84135
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
                                                                    let uu____84147
                                                                    =
                                                                    let uu____84148
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84148
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84147
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84150
                                                                    =
                                                                    let uu____84158
                                                                    =
                                                                    let uu____84159
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84160
                                                                    =
                                                                    let uu____84171
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84171)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84159
                                                                    uu____84160
                                                                     in
                                                                    (uu____84158,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84150
                                                                     in
                                                                    let uu____84184
                                                                    =
                                                                    let uu____84193
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84193
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84208
                                                                    =
                                                                    let uu____84211
                                                                    =
                                                                    let uu____84212
                                                                    =
                                                                    let uu____84220
                                                                    =
                                                                    let uu____84221
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84222
                                                                    =
                                                                    let uu____84233
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84233)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84221
                                                                    uu____84222
                                                                     in
                                                                    (uu____84220,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84212
                                                                     in
                                                                    [uu____84211]
                                                                     in
                                                                    (d3,
                                                                    uu____84208)
                                                                     in
                                                                    match uu____84184
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84135
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84290
                                                                    =
                                                                    let uu____84293
                                                                    =
                                                                    let uu____84296
                                                                    =
                                                                    let uu____84299
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84299
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84296
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84293
                                                                     in
                                                                    let uu____84306
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84290,
                                                                    uu____84306,
                                                                    env02))))))))))
                                      in
                                   let uu____84311 =
                                     let uu____84324 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84387  ->
                                          fun uu____84388  ->
                                            match (uu____84387, uu____84388)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84513 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84513 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84324
                                      in
                                   (match uu____84311 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84580 =
                                          let isDeclFun uu___640_84597 =
                                            match uu___640_84597 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84599 -> true
                                            | uu____84612 -> false  in
                                          let uu____84614 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84614
                                            (fun decls3  ->
                                               let uu____84644 =
                                                 FStar_List.fold_left
                                                   (fun uu____84675  ->
                                                      fun elt  ->
                                                        match uu____84675
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84716 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84716
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84744
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84744
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
                                                                    let uu___1459_84782
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84782.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84782.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84782.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84644 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84814 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84814, elts, rest))
                                           in
                                        (match uu____84580 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84843 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84849  ->
                                        match uu___641_84849 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84852 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84860 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84860)))
                                in
                             if uu____84843
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84882  ->
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
                   let uu____84921 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84921
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84940 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84940, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84996 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84996 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____85002 = encode_sigelt' env se  in
      match uu____85002 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____85014 =
                  let uu____85017 =
                    let uu____85018 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____85018  in
                  [uu____85017]  in
                FStar_All.pipe_right uu____85014
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____85023 ->
                let uu____85024 =
                  let uu____85027 =
                    let uu____85030 =
                      let uu____85031 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____85031  in
                    [uu____85030]  in
                  FStar_All.pipe_right uu____85027
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____85038 =
                  let uu____85041 =
                    let uu____85044 =
                      let uu____85047 =
                        let uu____85048 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____85048  in
                      [uu____85047]  in
                    FStar_All.pipe_right uu____85044
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____85041  in
                FStar_List.append uu____85024 uu____85038
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____85062 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____85062
       then
         let uu____85067 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____85067
       else ());
      (let is_opaque_to_smt t =
         let uu____85079 =
           let uu____85080 = FStar_Syntax_Subst.compress t  in
           uu____85080.FStar_Syntax_Syntax.n  in
         match uu____85079 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85085)) -> s = "opaque_to_smt"
         | uu____85090 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85099 =
           let uu____85100 = FStar_Syntax_Subst.compress t  in
           uu____85100.FStar_Syntax_Syntax.n  in
         match uu____85099 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85105)) -> s = "uninterpreted_by_smt"
         | uu____85110 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85116 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85122 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85134 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85135 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85136 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85149 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85151 =
             let uu____85153 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85153  in
           if uu____85151
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85182 ->
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
                let uu____85214 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85214 with
                | (formals,uu____85234) ->
                    let arity = FStar_List.length formals  in
                    let uu____85258 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85258 with
                     | (aname,atok,env2) ->
                         let uu____85284 =
                           let uu____85289 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85289 env2
                            in
                         (match uu____85284 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85301 =
                                  let uu____85302 =
                                    let uu____85314 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85334  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85314,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85302
                                   in
                                [uu____85301;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85351 =
                                let aux uu____85397 uu____85398 =
                                  match (uu____85397, uu____85398) with
                                  | ((bv,uu____85442),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85474 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85474 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85497 =
                                             let uu____85500 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85500 :: acc_sorts  in
                                           (env4, uu____85497, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85351 with
                               | (uu____85532,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85548 =
                                       let uu____85556 =
                                         let uu____85557 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85558 =
                                           let uu____85569 =
                                             let uu____85570 =
                                               let uu____85575 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85575)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85570
                                              in
                                           ([[app]], xs_sorts, uu____85569)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85557 uu____85558
                                          in
                                       (uu____85556,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85548
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85590 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85590
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85593 =
                                       let uu____85601 =
                                         let uu____85602 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85603 =
                                           let uu____85614 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85614)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85602 uu____85603
                                          in
                                       (uu____85601,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85593
                                      in
                                   let uu____85627 =
                                     let uu____85630 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85630  in
                                   (env2, uu____85627))))
                 in
              let uu____85639 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85639 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85665,uu____85666)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85667 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85667 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85689,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85696 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85702  ->
                       match uu___642_85702 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85705 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85711 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85714 -> false))
                in
             Prims.op_Negation uu____85696  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85724 =
                let uu____85729 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85729 env fv t quals  in
              match uu____85724 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85743 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85743  in
                  let uu____85746 =
                    let uu____85747 =
                      let uu____85750 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85750
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85747  in
                  (uu____85746, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85760 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85760 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85772 = env  in
                  let uu____85773 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85772.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85772.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85772.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85773;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85772.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85772.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85772.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85772.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85772.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85772.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85772.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85775 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85775 with
                 | (f3,decls) ->
                     let g =
                       let uu____85789 =
                         let uu____85792 =
                           let uu____85793 =
                             let uu____85801 =
                               let uu____85802 =
                                 let uu____85804 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85804
                                  in
                               FStar_Pervasives_Native.Some uu____85802  in
                             let uu____85808 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85801, uu____85808)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85793  in
                         [uu____85792]  in
                       FStar_All.pipe_right uu____85789
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85817) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85831 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85853 =
                        let uu____85856 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85856.FStar_Syntax_Syntax.fv_name  in
                      uu____85853.FStar_Syntax_Syntax.v  in
                    let uu____85857 =
                      let uu____85859 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85859  in
                    if uu____85857
                    then
                      let val_decl =
                        let uu___1629_85891 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85891.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85891.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85891.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85892 = encode_sigelt' env1 val_decl  in
                      match uu____85892 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85831 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85928,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85930;
                           FStar_Syntax_Syntax.lbtyp = uu____85931;
                           FStar_Syntax_Syntax.lbeff = uu____85932;
                           FStar_Syntax_Syntax.lbdef = uu____85933;
                           FStar_Syntax_Syntax.lbattrs = uu____85934;
                           FStar_Syntax_Syntax.lbpos = uu____85935;_}::[]),uu____85936)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85955 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85955 with
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
                  let uu____85993 =
                    let uu____85996 =
                      let uu____85997 =
                        let uu____86005 =
                          let uu____86006 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____86007 =
                            let uu____86018 =
                              let uu____86019 =
                                let uu____86024 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____86024)  in
                              FStar_SMTEncoding_Util.mkEq uu____86019  in
                            ([[b2t_x]], [xx], uu____86018)  in
                          FStar_SMTEncoding_Term.mkForall uu____86006
                            uu____86007
                           in
                        (uu____86005,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85997  in
                    [uu____85996]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85993
                   in
                let uu____86062 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____86062, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____86065,uu____86066) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86076  ->
                   match uu___643_86076 with
                   | FStar_Syntax_Syntax.Discriminator uu____86078 -> true
                   | uu____86080 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86082,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86094 =
                      let uu____86096 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86096.FStar_Ident.idText  in
                    uu____86094 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86103  ->
                      match uu___644_86103 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86106 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86109) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86123  ->
                   match uu___645_86123 with
                   | FStar_Syntax_Syntax.Projector uu____86125 -> true
                   | uu____86131 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86135 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86135 with
            | FStar_Pervasives_Native.Some uu____86142 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86144 = se  in
                  let uu____86145 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86145;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86144.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86144.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86144.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86148) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86163) ->
           let uu____86172 = encode_sigelts env ses  in
           (match uu____86172 with
            | (g,env1) ->
                let uu____86183 =
                  FStar_List.fold_left
                    (fun uu____86207  ->
                       fun elt  ->
                         match uu____86207 with
                         | (g',inversions) ->
                             let uu____86235 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86258  ->
                                       match uu___646_86258 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86260;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86261;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86262;_}
                                           -> false
                                       | uu____86269 -> true))
                                in
                             (match uu____86235 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86294 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86294.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86294.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86294.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86183 with
                 | (g',inversions) ->
                     let uu____86313 =
                       FStar_List.fold_left
                         (fun uu____86344  ->
                            fun elt  ->
                              match uu____86344 with
                              | (decls,elts,rest) ->
                                  let uu____86385 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86394  ->
                                            match uu___647_86394 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86396 -> true
                                            | uu____86409 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86385
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86432 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86453  ->
                                               match uu___648_86453 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86455 -> true
                                               | uu____86468 -> false))
                                        in
                                     match uu____86432 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86499 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86499.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86499.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86499.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86313 with
                      | (decls,elts,rest) ->
                          let uu____86525 =
                            let uu____86526 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86533 =
                              let uu____86536 =
                                let uu____86539 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86539  in
                              FStar_List.append elts uu____86536  in
                            FStar_List.append uu____86526 uu____86533  in
                          (uu____86525, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86550,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86563 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86563 with
             | (usubst,uvs) ->
                 let uu____86583 =
                   let uu____86590 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86591 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86592 =
                     let uu____86593 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86593 k  in
                   (uu____86590, uu____86591, uu____86592)  in
                 (match uu____86583 with
                  | (env1,tps1,k1) ->
                      let uu____86606 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86606 with
                       | (tps2,k2) ->
                           let uu____86614 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86614 with
                            | (uu____86630,k3) ->
                                let uu____86652 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86652 with
                                 | (tps3,env_tps,uu____86664,us) ->
                                     let u_k =
                                       let uu____86667 =
                                         let uu____86668 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86669 =
                                           let uu____86674 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86676 =
                                             let uu____86677 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86677
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86674 uu____86676
                                            in
                                         uu____86669
                                           FStar_Pervasives_Native.None
                                           uu____86668
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86667 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86697) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86703,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86706) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86714,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86721) ->
                                           let uu____86722 =
                                             let uu____86724 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86724
                                              in
                                           failwith uu____86722
                                       | (uu____86728,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86729 =
                                             let uu____86731 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86731
                                              in
                                           failwith uu____86729
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86735,uu____86736) ->
                                           let uu____86745 =
                                             let uu____86747 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86747
                                              in
                                           failwith uu____86745
                                       | (uu____86751,FStar_Syntax_Syntax.U_unif
                                          uu____86752) ->
                                           let uu____86761 =
                                             let uu____86763 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86763
                                              in
                                           failwith uu____86761
                                       | uu____86767 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86780 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86780 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86798 = u_leq_u_k u_tp  in
                                       if uu____86798
                                       then true
                                       else
                                         (let uu____86805 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86805 with
                                          | (formals,uu____86822) ->
                                              let uu____86843 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86843 with
                                               | (uu____86853,uu____86854,uu____86855,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86866 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86866
             then
               let uu____86871 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86871
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86891  ->
                       match uu___649_86891 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86895 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86908 = c  in
                 match uu____86908 with
                 | (name,args,uu____86913,uu____86914,uu____86915) ->
                     let uu____86926 =
                       let uu____86927 =
                         let uu____86939 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86966  ->
                                   match uu____86966 with
                                   | (uu____86975,sort,uu____86977) -> sort))
                            in
                         (name, uu____86939,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86927  in
                     [uu____86926]
               else
                 (let uu____86988 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____86988 c)
                in
             let inversion_axioms tapp vars =
               let uu____87006 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____87014 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____87014 FStar_Option.isNone))
                  in
               if uu____87006
               then []
               else
                 (let uu____87049 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____87049 with
                  | (xxsym,xx) ->
                      let uu____87062 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87101  ->
                                fun l  ->
                                  match uu____87101 with
                                  | (out,decls) ->
                                      let uu____87121 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87121 with
                                       | (uu____87132,data_t) ->
                                           let uu____87134 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87134 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87178 =
                                                    let uu____87179 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87179.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87178 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87182,indices)
                                                      -> indices
                                                  | uu____87208 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87238  ->
                                                            match uu____87238
                                                            with
                                                            | (x,uu____87246)
                                                                ->
                                                                let uu____87251
                                                                  =
                                                                  let uu____87252
                                                                    =
                                                                    let uu____87260
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87260,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87252
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87251)
                                                       env)
                                                   in
                                                let uu____87265 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87265 with
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
                                                                  let uu____87300
                                                                    =
                                                                    let uu____87305
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87305,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87300)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87308 =
                                                         let uu____87309 =
                                                           let uu____87314 =
                                                             let uu____87315
                                                               =
                                                               let uu____87320
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87321
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87320,
                                                                 uu____87321)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87315
                                                              in
                                                           (out, uu____87314)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87309
                                                          in
                                                       (uu____87308,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____87062 with
                       | (data_ax,decls) ->
                           let uu____87336 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87336 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87353 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87353 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87360 =
                                    let uu____87368 =
                                      let uu____87369 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87370 =
                                        let uu____87381 =
                                          let uu____87382 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87384 =
                                            let uu____87387 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87387 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87382 uu____87384
                                           in
                                        let uu____87389 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87381,
                                          uu____87389)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87369 uu____87370
                                       in
                                    let uu____87398 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87368,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87398)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87360
                                   in
                                let uu____87404 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87404)))
                in
             let uu____87411 =
               let uu____87416 =
                 let uu____87417 = FStar_Syntax_Subst.compress k  in
                 uu____87417.FStar_Syntax_Syntax.n  in
               match uu____87416 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87452 -> (tps, k)  in
             match uu____87411 with
             | (formals,res) ->
                 let uu____87459 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87459 with
                  | (formals1,res1) ->
                      let uu____87470 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87470 with
                       | (vars,guards,env',binder_decls,uu____87495) ->
                           let arity = FStar_List.length vars  in
                           let uu____87509 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87509 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87539 =
                                    let uu____87547 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87547)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87539
                                   in
                                let uu____87553 =
                                  let tname_decl =
                                    let uu____87563 =
                                      let uu____87564 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87583 =
                                                  let uu____87585 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87585
                                                   in
                                                let uu____87587 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87583, uu____87587,
                                                  false)))
                                         in
                                      let uu____87591 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87564,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87591, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87563
                                     in
                                  let uu____87599 =
                                    match vars with
                                    | [] ->
                                        let uu____87612 =
                                          let uu____87613 =
                                            let uu____87616 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87622  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87622) uu____87616
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87613
                                           in
                                        ([], uu____87612)
                                    | uu____87629 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87639 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87639
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87655 =
                                            let uu____87663 =
                                              let uu____87664 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87665 =
                                                let uu____87681 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87681)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87664 uu____87665
                                               in
                                            (uu____87663,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87655
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87599 with
                                  | (tok_decls,env2) ->
                                      let uu____87708 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87708
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87553 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87736 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87736 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87758 =
                                                 let uu____87759 =
                                                   let uu____87767 =
                                                     let uu____87768 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87768
                                                      in
                                                   (uu____87767,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87759
                                                  in
                                               [uu____87758]
                                             else []  in
                                           let uu____87776 =
                                             let uu____87779 =
                                               let uu____87782 =
                                                 let uu____87785 =
                                                   let uu____87786 =
                                                     let uu____87794 =
                                                       let uu____87795 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87796 =
                                                         let uu____87807 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87807)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87795
                                                         uu____87796
                                                        in
                                                     (uu____87794,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87786
                                                    in
                                                 [uu____87785]  in
                                               FStar_List.append karr
                                                 uu____87782
                                                in
                                             FStar_All.pipe_right uu____87779
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87776
                                        in
                                     let aux =
                                       let uu____87826 =
                                         let uu____87829 =
                                           inversion_axioms tapp vars  in
                                         let uu____87832 =
                                           let uu____87835 =
                                             let uu____87838 =
                                               let uu____87839 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87839 env2
                                                 tapp vars
                                                in
                                             [uu____87838]  in
                                           FStar_All.pipe_right uu____87835
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87829
                                           uu____87832
                                          in
                                       FStar_List.append kindingAx
                                         uu____87826
                                        in
                                     let g =
                                       let uu____87847 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87847
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87855,uu____87856,uu____87857,uu____87858,uu____87859)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87867,t,uu____87869,n_tps,uu____87871) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87881 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87881 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87929 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87929 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87957 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87957 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____87977 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____87977 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____88056 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____88056,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____88063 =
                                   let uu____88064 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____88064, true)
                                    in
                                 let uu____88072 =
                                   let uu____88079 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88079
                                    in
                                 FStar_All.pipe_right uu____88063 uu____88072
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
                               let uu____88091 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88091 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88103::uu____88104 ->
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
                                            let uu____88153 =
                                              let uu____88154 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88154]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88153
                                             in
                                          let uu____88180 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88181 =
                                            let uu____88192 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88192)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88180 uu____88181
                                      | uu____88219 -> tok_typing  in
                                    let uu____88230 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88230 with
                                     | (vars',guards',env'',decls_formals,uu____88255)
                                         ->
                                         let uu____88268 =
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
                                         (match uu____88268 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88298 ->
                                                    let uu____88307 =
                                                      let uu____88308 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88308
                                                       in
                                                    [uu____88307]
                                                 in
                                              let encode_elim uu____88324 =
                                                let uu____88325 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88325 with
                                                | (head1,args) ->
                                                    let uu____88376 =
                                                      let uu____88377 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88377.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88376 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88389;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88390;_},uu____88391)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88397 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88397
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
                                                                  | uu____88460
                                                                    ->
                                                                    let uu____88461
                                                                    =
                                                                    let uu____88467
                                                                    =
                                                                    let uu____88469
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88469
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88467)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88461
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88492
                                                                    =
                                                                    let uu____88494
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88494
                                                                     in
                                                                    if
                                                                    uu____88492
                                                                    then
                                                                    let uu____88516
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88516]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88519
                                                                =
                                                                let uu____88533
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88590
                                                                     ->
                                                                    fun
                                                                    uu____88591
                                                                     ->
                                                                    match 
                                                                    (uu____88590,
                                                                    uu____88591)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88702
                                                                    =
                                                                    let uu____88710
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88710
                                                                     in
                                                                    (match uu____88702
                                                                    with
                                                                    | 
                                                                    (uu____88724,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88735
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88735
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88740
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
                                                                  uu____88533
                                                                 in
                                                              (match uu____88519
                                                               with
                                                               | (uu____88761,arg_vars,elim_eqns_or_guards,uu____88764)
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
                                                                    let uu____88791
                                                                    =
                                                                    let uu____88799
                                                                    =
                                                                    let uu____88800
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88801
                                                                    =
                                                                    let uu____88812
                                                                    =
                                                                    let uu____88813
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88813
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88815
                                                                    =
                                                                    let uu____88816
                                                                    =
                                                                    let uu____88821
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88821)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88816
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88812,
                                                                    uu____88815)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88800
                                                                    uu____88801
                                                                     in
                                                                    (uu____88799,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88791
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88836
                                                                    =
                                                                    let uu____88837
                                                                    =
                                                                    let uu____88843
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88843,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88837
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88836
                                                                     in
                                                                    let uu____88846
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88846
                                                                    then
                                                                    let x =
                                                                    let uu____88850
                                                                    =
                                                                    let uu____88856
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88856,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88850
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88861
                                                                    =
                                                                    let uu____88869
                                                                    =
                                                                    let uu____88870
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88871
                                                                    =
                                                                    let uu____88882
                                                                    =
                                                                    let uu____88887
                                                                    =
                                                                    let uu____88890
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88890]
                                                                     in
                                                                    [uu____88887]
                                                                     in
                                                                    let uu____88895
                                                                    =
                                                                    let uu____88896
                                                                    =
                                                                    let uu____88901
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88903
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88901,
                                                                    uu____88903)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88896
                                                                     in
                                                                    (uu____88882,
                                                                    [x],
                                                                    uu____88895)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88870
                                                                    uu____88871
                                                                     in
                                                                    let uu____88924
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88869,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88924)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88861
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88935
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
                                                                    (let uu____88958
                                                                    =
                                                                    let uu____88959
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88959
                                                                    dapp1  in
                                                                    [uu____88958])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88935
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88966
                                                                    =
                                                                    let uu____88974
                                                                    =
                                                                    let uu____88975
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88976
                                                                    =
                                                                    let uu____88987
                                                                    =
                                                                    let uu____88988
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88988
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88990
                                                                    =
                                                                    let uu____88991
                                                                    =
                                                                    let uu____88996
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88996)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88991
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88987,
                                                                    uu____88990)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88975
                                                                    uu____88976
                                                                     in
                                                                    (uu____88974,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88966)
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
                                                         let uu____89015 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____89015
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
                                                                  | uu____89078
                                                                    ->
                                                                    let uu____89079
                                                                    =
                                                                    let uu____89085
                                                                    =
                                                                    let uu____89087
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89087
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89085)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89079
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89110
                                                                    =
                                                                    let uu____89112
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89112
                                                                     in
                                                                    if
                                                                    uu____89110
                                                                    then
                                                                    let uu____89134
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89134]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89137
                                                                =
                                                                let uu____89151
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89208
                                                                     ->
                                                                    fun
                                                                    uu____89209
                                                                     ->
                                                                    match 
                                                                    (uu____89208,
                                                                    uu____89209)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89320
                                                                    =
                                                                    let uu____89328
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89328
                                                                     in
                                                                    (match uu____89320
                                                                    with
                                                                    | 
                                                                    (uu____89342,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89353
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89353
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89358
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89358
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
                                                                  uu____89151
                                                                 in
                                                              (match uu____89137
                                                               with
                                                               | (uu____89379,arg_vars,elim_eqns_or_guards,uu____89382)
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
                                                                    let uu____89409
                                                                    =
                                                                    let uu____89417
                                                                    =
                                                                    let uu____89418
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89419
                                                                    =
                                                                    let uu____89430
                                                                    =
                                                                    let uu____89431
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89431
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89433
                                                                    =
                                                                    let uu____89434
                                                                    =
                                                                    let uu____89439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89439)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89434
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89430,
                                                                    uu____89433)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89418
                                                                    uu____89419
                                                                     in
                                                                    (uu____89417,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89409
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89454
                                                                    =
                                                                    let uu____89455
                                                                    =
                                                                    let uu____89461
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89461,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89455
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89454
                                                                     in
                                                                    let uu____89464
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89464
                                                                    then
                                                                    let x =
                                                                    let uu____89468
                                                                    =
                                                                    let uu____89474
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89474,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89468
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89479
                                                                    =
                                                                    let uu____89487
                                                                    =
                                                                    let uu____89488
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89489
                                                                    =
                                                                    let uu____89500
                                                                    =
                                                                    let uu____89505
                                                                    =
                                                                    let uu____89508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89508]
                                                                     in
                                                                    [uu____89505]
                                                                     in
                                                                    let uu____89513
                                                                    =
                                                                    let uu____89514
                                                                    =
                                                                    let uu____89519
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89521
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89519,
                                                                    uu____89521)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89514
                                                                     in
                                                                    (uu____89500,
                                                                    [x],
                                                                    uu____89513)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89488
                                                                    uu____89489
                                                                     in
                                                                    let uu____89542
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89487,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89542)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89479
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89553
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
                                                                    (let uu____89576
                                                                    =
                                                                    let uu____89577
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89577
                                                                    dapp1  in
                                                                    [uu____89576])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89553
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89584
                                                                    =
                                                                    let uu____89592
                                                                    =
                                                                    let uu____89593
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89594
                                                                    =
                                                                    let uu____89605
                                                                    =
                                                                    let uu____89606
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89606
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89608
                                                                    =
                                                                    let uu____89609
                                                                    =
                                                                    let uu____89614
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89614)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89609
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89605,
                                                                    uu____89608)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89593
                                                                    uu____89594
                                                                     in
                                                                    (uu____89592,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89584)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89631 ->
                                                         ((let uu____89633 =
                                                             let uu____89639
                                                               =
                                                               let uu____89641
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89643
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89641
                                                                 uu____89643
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89639)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89633);
                                                          ([], [])))
                                                 in
                                              let uu____89651 =
                                                encode_elim ()  in
                                              (match uu____89651 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89677 =
                                                       let uu____89680 =
                                                         let uu____89683 =
                                                           let uu____89686 =
                                                             let uu____89689
                                                               =
                                                               let uu____89692
                                                                 =
                                                                 let uu____89695
                                                                   =
                                                                   let uu____89696
                                                                    =
                                                                    let uu____89708
                                                                    =
                                                                    let uu____89709
                                                                    =
                                                                    let uu____89711
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89711
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89709
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89708)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89696
                                                                    in
                                                                 [uu____89695]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89692
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89689
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89722 =
                                                             let uu____89725
                                                               =
                                                               let uu____89728
                                                                 =
                                                                 let uu____89731
                                                                   =
                                                                   let uu____89734
                                                                    =
                                                                    let uu____89737
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89742
                                                                    =
                                                                    let uu____89745
                                                                    =
                                                                    let uu____89746
                                                                    =
                                                                    let uu____89754
                                                                    =
                                                                    let uu____89755
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89756
                                                                    =
                                                                    let uu____89767
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89767)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89755
                                                                    uu____89756
                                                                     in
                                                                    (uu____89754,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89746
                                                                     in
                                                                    let uu____89780
                                                                    =
                                                                    let uu____89783
                                                                    =
                                                                    let uu____89784
                                                                    =
                                                                    let uu____89792
                                                                    =
                                                                    let uu____89793
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89794
                                                                    =
                                                                    let uu____89805
                                                                    =
                                                                    let uu____89806
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89806
                                                                    vars'  in
                                                                    let uu____89808
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89805,
                                                                    uu____89808)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89793
                                                                    uu____89794
                                                                     in
                                                                    (uu____89792,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89784
                                                                     in
                                                                    [uu____89783]
                                                                     in
                                                                    uu____89745
                                                                    ::
                                                                    uu____89780
                                                                     in
                                                                    uu____89737
                                                                    ::
                                                                    uu____89742
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89734
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89731
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89728
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89725
                                                              in
                                                           FStar_List.append
                                                             uu____89686
                                                             uu____89722
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89683
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89680
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89677
                                                      in
                                                   let uu____89825 =
                                                     let uu____89826 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89826 g
                                                      in
                                                   (uu____89825, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89860  ->
              fun se  ->
                match uu____89860 with
                | (g,env1) ->
                    let uu____89880 = encode_sigelt env1 se  in
                    (match uu____89880 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89948 =
        match uu____89948 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____89985 ->
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
                 ((let uu____89993 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____89993
                   then
                     let uu____89998 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____90000 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____90002 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____89998 uu____90000 uu____90002
                   else ());
                  (let uu____90007 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____90007 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____90025 =
                         let uu____90033 =
                           let uu____90035 =
                             let uu____90037 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____90037
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____90035  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____90033
                          in
                       (match uu____90025 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____90057 = FStar_Options.log_queries ()
                                 in
                              if uu____90057
                              then
                                let uu____90060 =
                                  let uu____90062 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____90064 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____90066 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____90062 uu____90064 uu____90066
                                   in
                                FStar_Pervasives_Native.Some uu____90060
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90082 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90092 =
                                let uu____90095 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90095  in
                              FStar_List.append uu____90082 uu____90092  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90107,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90127 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90127 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90148 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90148 with | (uu____90175,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90228  ->
              match uu____90228 with
              | (l,uu____90237,uu____90238) ->
                  let uu____90241 =
                    let uu____90253 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90253, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90241))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90286  ->
              match uu____90286 with
              | (l,uu____90297,uu____90298) ->
                  let uu____90301 =
                    let uu____90302 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90305  -> FStar_SMTEncoding_Term.Echo _90305)
                      uu____90302
                     in
                  let uu____90306 =
                    let uu____90309 =
                      let uu____90310 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90310  in
                    [uu____90309]  in
                  uu____90301 :: uu____90306))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90339 =
      let uu____90342 =
        let uu____90343 = FStar_Util.psmap_empty ()  in
        let uu____90358 =
          let uu____90367 = FStar_Util.psmap_empty ()  in (uu____90367, [])
           in
        let uu____90374 =
          let uu____90376 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90376 FStar_Ident.string_of_lid  in
        let uu____90378 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90343;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90358;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90374;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90378
        }  in
      [uu____90342]  in
    FStar_ST.op_Colon_Equals last_env uu____90339
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90422 = FStar_ST.op_Bang last_env  in
      match uu____90422 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90450 ->
          let uu___2175_90453 = e  in
          let uu____90454 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90453.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90453.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90453.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90453.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90453.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90453.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90453.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90454;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90453.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90453.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90462 = FStar_ST.op_Bang last_env  in
    match uu____90462 with
    | [] -> failwith "Empty env stack"
    | uu____90489::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90521  ->
    let uu____90522 = FStar_ST.op_Bang last_env  in
    match uu____90522 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90582  ->
    let uu____90583 = FStar_ST.op_Bang last_env  in
    match uu____90583 with
    | [] -> failwith "Popping an empty stack"
    | uu____90610::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90647  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90700  ->
         let uu____90701 = snapshot_env ()  in
         match uu____90701 with
         | (env_depth,()) ->
             let uu____90723 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90723 with
              | (varops_depth,()) ->
                  let uu____90745 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90745 with
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
        (fun uu____90803  ->
           let uu____90804 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90804 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90899 = snapshot msg  in () 
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
        | (uu____90945::uu____90946,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90954 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90954.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90954.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90954.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90955 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_90982 = elt  in
        let uu____90983 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_90982.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_90982.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____90983;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_90982.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____91003 =
        let uu____91006 =
          let uu____91007 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____91007  in
        let uu____91008 = open_fact_db_tags env  in uu____91006 ::
          uu____91008
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____91003
  
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
      let uu____91035 = encode_sigelt env se  in
      match uu____91035 with
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
                (let uu____91081 =
                   let uu____91084 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91084
                    in
                 match uu____91081 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91099 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91099
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91129 = FStar_Options.log_queries ()  in
        if uu____91129
        then
          let uu____91134 =
            let uu____91135 =
              let uu____91137 =
                let uu____91139 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91139 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91137  in
            FStar_SMTEncoding_Term.Caption uu____91135  in
          uu____91134 :: decls
        else decls  in
      (let uu____91158 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91158
       then
         let uu____91161 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91161
       else ());
      (let env =
         let uu____91167 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91167 tcenv  in
       let uu____91168 = encode_top_level_facts env se  in
       match uu____91168 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91182 =
               let uu____91185 =
                 let uu____91188 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91188
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91185  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91182)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91221 = FStar_Options.log_queries ()  in
          if uu____91221
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91241 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91241.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91241.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91241.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91241.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91241.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91241.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91241.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91241.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91241.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91241.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91246 =
             let uu____91249 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91249
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91246  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91269 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91269
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
          (let uu____91293 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91293
           then
             let uu____91296 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91296
           else ());
          (let env =
             let uu____91304 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91304
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91343  ->
                     fun se  ->
                       match uu____91343 with
                       | (g,env2) ->
                           let uu____91363 = encode_top_level_facts env2 se
                              in
                           (match uu____91363 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91386 =
             encode_signature
               (let uu___2303_91395 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91395.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91395.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91395.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91395.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91395.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91395.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91395.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91395.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91395.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91395.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91386 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91411 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91411
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91417 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91417))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91445  ->
        match uu____91445 with
        | (decls,fvbs) ->
            ((let uu____91459 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91459
              then ()
              else
                (let uu____91464 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91464
                 then
                   let uu____91467 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91467
                 else ()));
             (let env =
                let uu____91475 = get_env name tcenv  in
                FStar_All.pipe_right uu____91475
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91477 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91477
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91491 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91491
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
        (let uu____91553 =
           let uu____91555 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91555.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91553);
        (let env =
           let uu____91557 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91557 tcenv  in
         let uu____91558 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91597 = aux rest  in
                 (match uu____91597 with
                  | (out,rest1) ->
                      let t =
                        let uu____91625 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91625 with
                        | FStar_Pervasives_Native.Some uu____91628 ->
                            let uu____91629 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91629
                              x.FStar_Syntax_Syntax.sort
                        | uu____91630 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91634 =
                        let uu____91637 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91640 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91640.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91640.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91637 :: out  in
                      (uu____91634, rest1))
             | uu____91645 -> ([], bindings)  in
           let uu____91652 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91652 with
           | (closing,bindings) ->
               let uu____91679 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91679, bindings)
            in
         match uu____91558 with
         | (q1,bindings) ->
             let uu____91710 = encode_env_bindings env bindings  in
             (match uu____91710 with
              | (env_decls,env1) ->
                  ((let uu____91732 =
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
                    if uu____91732
                    then
                      let uu____91739 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91739
                    else ());
                   (let uu____91744 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91744 with
                    | (phi,qdecls) ->
                        let uu____91765 =
                          let uu____91770 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91770 phi
                           in
                        (match uu____91765 with
                         | (labels,phi1) ->
                             let uu____91787 = encode_labels labels  in
                             (match uu____91787 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91823 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91823
                                    then
                                      let uu____91828 =
                                        let uu____91829 =
                                          let uu____91831 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91831
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91829
                                         in
                                      [uu____91828]
                                    else []  in
                                  let query_prelude =
                                    let uu____91839 =
                                      let uu____91840 =
                                        let uu____91841 =
                                          let uu____91844 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91851 =
                                            let uu____91854 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91854
                                             in
                                          FStar_List.append uu____91844
                                            uu____91851
                                           in
                                        FStar_List.append env_decls
                                          uu____91841
                                         in
                                      FStar_All.pipe_right uu____91840
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91839
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91864 =
                                      let uu____91872 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91873 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91872,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91873)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91864
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
  