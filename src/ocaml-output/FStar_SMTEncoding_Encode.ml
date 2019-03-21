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
  let uu____67927 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67927 with
  | (asym,a) ->
      let uu____67938 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67938 with
       | (xsym,x) ->
           let uu____67949 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67949 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____68027 =
                      let uu____68039 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____68039, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____68027  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68059 =
                      let uu____68067 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68067)  in
                    FStar_SMTEncoding_Util.mkApp uu____68059  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68086 =
                    let uu____68089 =
                      let uu____68092 =
                        let uu____68095 =
                          let uu____68096 =
                            let uu____68104 =
                              let uu____68105 =
                                let uu____68116 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68116)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68105
                               in
                            (uu____68104, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68096  in
                        let uu____68128 =
                          let uu____68131 =
                            let uu____68132 =
                              let uu____68140 =
                                let uu____68141 =
                                  let uu____68152 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68152)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68141
                                 in
                              (uu____68140,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68132  in
                          [uu____68131]  in
                        uu____68095 :: uu____68128  in
                      xtok_decl :: uu____68092  in
                    xname_decl :: uu____68089  in
                  (xtok1, (FStar_List.length vars), uu____68086)  in
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
                  let uu____68322 =
                    let uu____68343 =
                      let uu____68362 =
                        let uu____68363 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68363
                         in
                      quant axy uu____68362  in
                    (FStar_Parser_Const.op_Eq, uu____68343)  in
                  let uu____68380 =
                    let uu____68403 =
                      let uu____68424 =
                        let uu____68443 =
                          let uu____68444 =
                            let uu____68445 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68445  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68444
                           in
                        quant axy uu____68443  in
                      (FStar_Parser_Const.op_notEq, uu____68424)  in
                    let uu____68462 =
                      let uu____68485 =
                        let uu____68506 =
                          let uu____68525 =
                            let uu____68526 =
                              let uu____68527 =
                                let uu____68532 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68533 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68532, uu____68533)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68527  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68526
                             in
                          quant xy uu____68525  in
                        (FStar_Parser_Const.op_And, uu____68506)  in
                      let uu____68550 =
                        let uu____68573 =
                          let uu____68594 =
                            let uu____68613 =
                              let uu____68614 =
                                let uu____68615 =
                                  let uu____68620 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68621 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68620, uu____68621)  in
                                FStar_SMTEncoding_Util.mkOr uu____68615  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68614
                               in
                            quant xy uu____68613  in
                          (FStar_Parser_Const.op_Or, uu____68594)  in
                        let uu____68638 =
                          let uu____68661 =
                            let uu____68682 =
                              let uu____68701 =
                                let uu____68702 =
                                  let uu____68703 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68703
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68702
                                 in
                              quant qx uu____68701  in
                            (FStar_Parser_Const.op_Negation, uu____68682)  in
                          let uu____68720 =
                            let uu____68743 =
                              let uu____68764 =
                                let uu____68783 =
                                  let uu____68784 =
                                    let uu____68785 =
                                      let uu____68790 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68791 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68790, uu____68791)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68785
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68784
                                   in
                                quant xy uu____68783  in
                              (FStar_Parser_Const.op_LT, uu____68764)  in
                            let uu____68808 =
                              let uu____68831 =
                                let uu____68852 =
                                  let uu____68871 =
                                    let uu____68872 =
                                      let uu____68873 =
                                        let uu____68878 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68879 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68878, uu____68879)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68873
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68872
                                     in
                                  quant xy uu____68871  in
                                (FStar_Parser_Const.op_LTE, uu____68852)  in
                              let uu____68896 =
                                let uu____68919 =
                                  let uu____68940 =
                                    let uu____68959 =
                                      let uu____68960 =
                                        let uu____68961 =
                                          let uu____68966 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68967 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68966, uu____68967)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68961
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68960
                                       in
                                    quant xy uu____68959  in
                                  (FStar_Parser_Const.op_GT, uu____68940)  in
                                let uu____68984 =
                                  let uu____69007 =
                                    let uu____69028 =
                                      let uu____69047 =
                                        let uu____69048 =
                                          let uu____69049 =
                                            let uu____69054 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69055 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69054, uu____69055)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69049
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69048
                                         in
                                      quant xy uu____69047  in
                                    (FStar_Parser_Const.op_GTE, uu____69028)
                                     in
                                  let uu____69072 =
                                    let uu____69095 =
                                      let uu____69116 =
                                        let uu____69135 =
                                          let uu____69136 =
                                            let uu____69137 =
                                              let uu____69142 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69143 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69142, uu____69143)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69137
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69136
                                           in
                                        quant xy uu____69135  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69116)
                                       in
                                    let uu____69160 =
                                      let uu____69183 =
                                        let uu____69204 =
                                          let uu____69223 =
                                            let uu____69224 =
                                              let uu____69225 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69225
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69224
                                             in
                                          quant qx uu____69223  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69204)
                                         in
                                      let uu____69242 =
                                        let uu____69265 =
                                          let uu____69286 =
                                            let uu____69305 =
                                              let uu____69306 =
                                                let uu____69307 =
                                                  let uu____69312 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69313 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69312, uu____69313)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69307
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69306
                                               in
                                            quant xy uu____69305  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69286)
                                           in
                                        let uu____69330 =
                                          let uu____69353 =
                                            let uu____69374 =
                                              let uu____69393 =
                                                let uu____69394 =
                                                  let uu____69395 =
                                                    let uu____69400 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69401 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69400,
                                                      uu____69401)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69395
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69394
                                                 in
                                              quant xy uu____69393  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69374)
                                             in
                                          let uu____69418 =
                                            let uu____69441 =
                                              let uu____69462 =
                                                let uu____69481 =
                                                  let uu____69482 =
                                                    let uu____69483 =
                                                      let uu____69488 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69489 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69488,
                                                        uu____69489)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69483
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69482
                                                   in
                                                quant xy uu____69481  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69462)
                                               in
                                            let uu____69506 =
                                              let uu____69529 =
                                                let uu____69550 =
                                                  let uu____69569 =
                                                    let uu____69570 =
                                                      let uu____69571 =
                                                        let uu____69576 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69577 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69576,
                                                          uu____69577)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69571
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69570
                                                     in
                                                  quant xy uu____69569  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69550)
                                                 in
                                              let uu____69594 =
                                                let uu____69617 =
                                                  let uu____69638 =
                                                    let uu____69657 =
                                                      let uu____69658 =
                                                        let uu____69659 =
                                                          let uu____69664 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69665 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69664,
                                                            uu____69665)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69659
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69658
                                                       in
                                                    quant xy uu____69657  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69638)
                                                   in
                                                let uu____69682 =
                                                  let uu____69705 =
                                                    let uu____69726 =
                                                      let uu____69745 =
                                                        let uu____69746 =
                                                          let uu____69747 =
                                                            let uu____69752 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69753 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69752,
                                                              uu____69753)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69747
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69746
                                                         in
                                                      quant xy uu____69745
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69726)
                                                     in
                                                  let uu____69770 =
                                                    let uu____69793 =
                                                      let uu____69814 =
                                                        let uu____69833 =
                                                          let uu____69834 =
                                                            let uu____69835 =
                                                              let uu____69840
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69841
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69840,
                                                                uu____69841)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69835
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69834
                                                           in
                                                        quant xy uu____69833
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69814)
                                                       in
                                                    let uu____69858 =
                                                      let uu____69881 =
                                                        let uu____69902 =
                                                          let uu____69921 =
                                                            let uu____69922 =
                                                              let uu____69923
                                                                =
                                                                let uu____69928
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69929
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69928,
                                                                  uu____69929)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69923
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69922
                                                             in
                                                          quant xy
                                                            uu____69921
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69902)
                                                         in
                                                      let uu____69946 =
                                                        let uu____69969 =
                                                          let uu____69990 =
                                                            let uu____70009 =
                                                              let uu____70010
                                                                =
                                                                let uu____70011
                                                                  =
                                                                  let uu____70016
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____70017
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____70016,
                                                                    uu____70017)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____70011
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____70010
                                                               in
                                                            quant xy
                                                              uu____70009
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69990)
                                                           in
                                                        let uu____70034 =
                                                          let uu____70057 =
                                                            let uu____70078 =
                                                              let uu____70097
                                                                =
                                                                let uu____70098
                                                                  =
                                                                  let uu____70099
                                                                    =
                                                                    let uu____70104
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70105
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70104,
                                                                    uu____70105)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70099
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70098
                                                                 in
                                                              quant xy
                                                                uu____70097
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70078)
                                                             in
                                                          let uu____70122 =
                                                            let uu____70145 =
                                                              let uu____70166
                                                                =
                                                                let uu____70185
                                                                  =
                                                                  let uu____70186
                                                                    =
                                                                    let uu____70187
                                                                    =
                                                                    let uu____70192
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70193
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70192,
                                                                    uu____70193)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70187
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70186
                                                                   in
                                                                quant xy
                                                                  uu____70185
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70166)
                                                               in
                                                            let uu____70210 =
                                                              let uu____70233
                                                                =
                                                                let uu____70254
                                                                  =
                                                                  let uu____70273
                                                                    =
                                                                    let uu____70274
                                                                    =
                                                                    let uu____70275
                                                                    =
                                                                    let uu____70280
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70281
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70280,
                                                                    uu____70281)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70275
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70274
                                                                     in
                                                                  quant xy
                                                                    uu____70273
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70254)
                                                                 in
                                                              let uu____70298
                                                                =
                                                                let uu____70321
                                                                  =
                                                                  let uu____70342
                                                                    =
                                                                    let uu____70361
                                                                    =
                                                                    let uu____70362
                                                                    =
                                                                    let uu____70363
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70363
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70362
                                                                     in
                                                                    quant qx
                                                                    uu____70361
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70342)
                                                                   in
                                                                [uu____70321]
                                                                 in
                                                              uu____70233 ::
                                                                uu____70298
                                                               in
                                                            uu____70145 ::
                                                              uu____70210
                                                             in
                                                          uu____70057 ::
                                                            uu____70122
                                                           in
                                                        uu____69969 ::
                                                          uu____70034
                                                         in
                                                      uu____69881 ::
                                                        uu____69946
                                                       in
                                                    uu____69793 ::
                                                      uu____69858
                                                     in
                                                  uu____69705 :: uu____69770
                                                   in
                                                uu____69617 :: uu____69682
                                                 in
                                              uu____69529 :: uu____69594  in
                                            uu____69441 :: uu____69506  in
                                          uu____69353 :: uu____69418  in
                                        uu____69265 :: uu____69330  in
                                      uu____69183 :: uu____69242  in
                                    uu____69095 :: uu____69160  in
                                  uu____69007 :: uu____69072  in
                                uu____68919 :: uu____68984  in
                              uu____68831 :: uu____68896  in
                            uu____68743 :: uu____68808  in
                          uu____68661 :: uu____68720  in
                        uu____68573 :: uu____68638  in
                      uu____68485 :: uu____68550  in
                    uu____68403 :: uu____68462  in
                  uu____68322 :: uu____68380  in
                let mk1 l v1 =
                  let uu____70902 =
                    let uu____70914 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____71004  ->
                              match uu____71004 with
                              | (l',uu____71025) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70914
                      (FStar_Option.map
                         (fun uu____71124  ->
                            match uu____71124 with
                            | (uu____71152,b) ->
                                let uu____71186 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71186 v1))
                     in
                  FStar_All.pipe_right uu____70902 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71269  ->
                          match uu____71269 with
                          | (l',uu____71290) -> FStar_Ident.lid_equals l l'))
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
          let uu____71364 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71364 with
          | (xxsym,xx) ->
              let uu____71375 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71375 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71391 =
                     let uu____71399 =
                       let uu____71400 =
                         let uu____71411 =
                           let uu____71412 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71422 =
                             let uu____71433 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71433 :: vars  in
                           uu____71412 :: uu____71422  in
                         let uu____71459 =
                           let uu____71460 =
                             let uu____71465 =
                               let uu____71466 =
                                 let uu____71471 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71471)  in
                               FStar_SMTEncoding_Util.mkEq uu____71466  in
                             (xx_has_type, uu____71465)  in
                           FStar_SMTEncoding_Util.mkImp uu____71460  in
                         ([[xx_has_type]], uu____71411, uu____71459)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71400  in
                     let uu____71484 =
                       let uu____71486 =
                         let uu____71488 =
                           let uu____71490 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71490  in
                         Prims.op_Hat module_name uu____71488  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71486
                        in
                     (uu____71399,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71484)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71391)
  
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
    let uu____71546 =
      let uu____71548 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71548  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71546  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71570 =
      let uu____71571 =
        let uu____71579 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71579, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71571  in
    let uu____71584 =
      let uu____71587 =
        let uu____71588 =
          let uu____71596 =
            let uu____71597 =
              let uu____71608 =
                let uu____71609 =
                  let uu____71614 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71614)  in
                FStar_SMTEncoding_Util.mkImp uu____71609  in
              ([[typing_pred]], [xx], uu____71608)  in
            let uu____71639 =
              let uu____71654 = FStar_TypeChecker_Env.get_range env  in
              let uu____71655 = mkForall_fuel1 env  in
              uu____71655 uu____71654  in
            uu____71639 uu____71597  in
          (uu____71596, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71588  in
      [uu____71587]  in
    uu____71570 :: uu____71584  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71702 =
      let uu____71703 =
        let uu____71711 =
          let uu____71712 = FStar_TypeChecker_Env.get_range env  in
          let uu____71713 =
            let uu____71724 =
              let uu____71729 =
                let uu____71732 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71732]  in
              [uu____71729]  in
            let uu____71737 =
              let uu____71738 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71738 tt  in
            (uu____71724, [bb], uu____71737)  in
          FStar_SMTEncoding_Term.mkForall uu____71712 uu____71713  in
        (uu____71711, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71703  in
    let uu____71763 =
      let uu____71766 =
        let uu____71767 =
          let uu____71775 =
            let uu____71776 =
              let uu____71787 =
                let uu____71788 =
                  let uu____71793 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71793)  in
                FStar_SMTEncoding_Util.mkImp uu____71788  in
              ([[typing_pred]], [xx], uu____71787)  in
            let uu____71820 =
              let uu____71835 = FStar_TypeChecker_Env.get_range env  in
              let uu____71836 = mkForall_fuel1 env  in
              uu____71836 uu____71835  in
            uu____71820 uu____71776  in
          (uu____71775, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71767  in
      [uu____71766]  in
    uu____71702 :: uu____71763  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71879 =
        let uu____71880 =
          let uu____71886 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71886, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71880  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71879  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71900 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71900  in
    let uu____71905 =
      let uu____71906 =
        let uu____71914 =
          let uu____71915 = FStar_TypeChecker_Env.get_range env  in
          let uu____71916 =
            let uu____71927 =
              let uu____71932 =
                let uu____71935 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71935]  in
              [uu____71932]  in
            let uu____71940 =
              let uu____71941 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71941 tt  in
            (uu____71927, [bb], uu____71940)  in
          FStar_SMTEncoding_Term.mkForall uu____71915 uu____71916  in
        (uu____71914, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71906  in
    let uu____71966 =
      let uu____71969 =
        let uu____71970 =
          let uu____71978 =
            let uu____71979 =
              let uu____71990 =
                let uu____71991 =
                  let uu____71996 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71996)  in
                FStar_SMTEncoding_Util.mkImp uu____71991  in
              ([[typing_pred]], [xx], uu____71990)  in
            let uu____72023 =
              let uu____72038 = FStar_TypeChecker_Env.get_range env  in
              let uu____72039 = mkForall_fuel1 env  in
              uu____72039 uu____72038  in
            uu____72023 uu____71979  in
          (uu____71978, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71970  in
      let uu____72061 =
        let uu____72064 =
          let uu____72065 =
            let uu____72073 =
              let uu____72074 =
                let uu____72085 =
                  let uu____72086 =
                    let uu____72091 =
                      let uu____72092 =
                        let uu____72095 =
                          let uu____72098 =
                            let uu____72101 =
                              let uu____72102 =
                                let uu____72107 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72108 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72107, uu____72108)  in
                              FStar_SMTEncoding_Util.mkGT uu____72102  in
                            let uu____72110 =
                              let uu____72113 =
                                let uu____72114 =
                                  let uu____72119 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72120 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72119, uu____72120)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72114  in
                              let uu____72122 =
                                let uu____72125 =
                                  let uu____72126 =
                                    let uu____72131 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72132 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72131, uu____72132)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72126  in
                                [uu____72125]  in
                              uu____72113 :: uu____72122  in
                            uu____72101 :: uu____72110  in
                          typing_pred_y :: uu____72098  in
                        typing_pred :: uu____72095  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72092  in
                    (uu____72091, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72086  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72085)
                 in
              let uu____72165 =
                let uu____72180 = FStar_TypeChecker_Env.get_range env  in
                let uu____72181 = mkForall_fuel1 env  in
                uu____72181 uu____72180  in
              uu____72165 uu____72074  in
            (uu____72073,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72065  in
        [uu____72064]  in
      uu____71969 :: uu____72061  in
    uu____71905 :: uu____71966  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72224 =
        let uu____72225 =
          let uu____72231 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72231, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72225  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72224  in
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
      let uu____72247 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72247  in
    let uu____72252 =
      let uu____72253 =
        let uu____72261 =
          let uu____72262 = FStar_TypeChecker_Env.get_range env  in
          let uu____72263 =
            let uu____72274 =
              let uu____72279 =
                let uu____72282 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72282]  in
              [uu____72279]  in
            let uu____72287 =
              let uu____72288 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72288 tt  in
            (uu____72274, [bb], uu____72287)  in
          FStar_SMTEncoding_Term.mkForall uu____72262 uu____72263  in
        (uu____72261, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72253  in
    let uu____72313 =
      let uu____72316 =
        let uu____72317 =
          let uu____72325 =
            let uu____72326 =
              let uu____72337 =
                let uu____72338 =
                  let uu____72343 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72343)  in
                FStar_SMTEncoding_Util.mkImp uu____72338  in
              ([[typing_pred]], [xx], uu____72337)  in
            let uu____72370 =
              let uu____72385 = FStar_TypeChecker_Env.get_range env  in
              let uu____72386 = mkForall_fuel1 env  in
              uu____72386 uu____72385  in
            uu____72370 uu____72326  in
          (uu____72325, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72317  in
      let uu____72408 =
        let uu____72411 =
          let uu____72412 =
            let uu____72420 =
              let uu____72421 =
                let uu____72432 =
                  let uu____72433 =
                    let uu____72438 =
                      let uu____72439 =
                        let uu____72442 =
                          let uu____72445 =
                            let uu____72448 =
                              let uu____72449 =
                                let uu____72454 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72455 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72454, uu____72455)  in
                              FStar_SMTEncoding_Util.mkGT uu____72449  in
                            let uu____72457 =
                              let uu____72460 =
                                let uu____72461 =
                                  let uu____72466 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72467 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72466, uu____72467)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72461  in
                              let uu____72469 =
                                let uu____72472 =
                                  let uu____72473 =
                                    let uu____72478 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72479 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72478, uu____72479)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72473  in
                                [uu____72472]  in
                              uu____72460 :: uu____72469  in
                            uu____72448 :: uu____72457  in
                          typing_pred_y :: uu____72445  in
                        typing_pred :: uu____72442  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72439  in
                    (uu____72438, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72433  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72432)
                 in
              let uu____72512 =
                let uu____72527 = FStar_TypeChecker_Env.get_range env  in
                let uu____72528 = mkForall_fuel1 env  in
                uu____72528 uu____72527  in
              uu____72512 uu____72421  in
            (uu____72420,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72412  in
        [uu____72411]  in
      uu____72316 :: uu____72408  in
    uu____72252 :: uu____72313  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72575 =
      let uu____72576 =
        let uu____72584 =
          let uu____72585 = FStar_TypeChecker_Env.get_range env  in
          let uu____72586 =
            let uu____72597 =
              let uu____72602 =
                let uu____72605 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72605]  in
              [uu____72602]  in
            let uu____72610 =
              let uu____72611 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72611 tt  in
            (uu____72597, [bb], uu____72610)  in
          FStar_SMTEncoding_Term.mkForall uu____72585 uu____72586  in
        (uu____72584, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72576  in
    let uu____72636 =
      let uu____72639 =
        let uu____72640 =
          let uu____72648 =
            let uu____72649 =
              let uu____72660 =
                let uu____72661 =
                  let uu____72666 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72666)  in
                FStar_SMTEncoding_Util.mkImp uu____72661  in
              ([[typing_pred]], [xx], uu____72660)  in
            let uu____72693 =
              let uu____72708 = FStar_TypeChecker_Env.get_range env  in
              let uu____72709 = mkForall_fuel1 env  in
              uu____72709 uu____72708  in
            uu____72693 uu____72649  in
          (uu____72648, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72640  in
      [uu____72639]  in
    uu____72575 :: uu____72636  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72756 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72756]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72786 =
      let uu____72787 =
        let uu____72795 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72795, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72787  in
    [uu____72786]  in
  let mk_and_interp env conj uu____72818 =
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
    let uu____72847 =
      let uu____72848 =
        let uu____72856 =
          let uu____72857 = FStar_TypeChecker_Env.get_range env  in
          let uu____72858 =
            let uu____72869 =
              let uu____72870 =
                let uu____72875 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72875, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72870  in
            ([[l_and_a_b]], [aa; bb], uu____72869)  in
          FStar_SMTEncoding_Term.mkForall uu____72857 uu____72858  in
        (uu____72856, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72848  in
    [uu____72847]  in
  let mk_or_interp env disj uu____72930 =
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
    let uu____72959 =
      let uu____72960 =
        let uu____72968 =
          let uu____72969 = FStar_TypeChecker_Env.get_range env  in
          let uu____72970 =
            let uu____72981 =
              let uu____72982 =
                let uu____72987 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72987, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72982  in
            ([[l_or_a_b]], [aa; bb], uu____72981)  in
          FStar_SMTEncoding_Term.mkForall uu____72969 uu____72970  in
        (uu____72968, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72960  in
    [uu____72959]  in
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
    let uu____73065 =
      let uu____73066 =
        let uu____73074 =
          let uu____73075 = FStar_TypeChecker_Env.get_range env  in
          let uu____73076 =
            let uu____73087 =
              let uu____73088 =
                let uu____73093 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73093, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73088  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73087)  in
          FStar_SMTEncoding_Term.mkForall uu____73075 uu____73076  in
        (uu____73074, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73066  in
    [uu____73065]  in
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
    let uu____73183 =
      let uu____73184 =
        let uu____73192 =
          let uu____73193 = FStar_TypeChecker_Env.get_range env  in
          let uu____73194 =
            let uu____73205 =
              let uu____73206 =
                let uu____73211 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73211, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73206  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73205)  in
          FStar_SMTEncoding_Term.mkForall uu____73193 uu____73194  in
        (uu____73192, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73184  in
    [uu____73183]  in
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
    let uu____73311 =
      let uu____73312 =
        let uu____73320 =
          let uu____73321 = FStar_TypeChecker_Env.get_range env  in
          let uu____73322 =
            let uu____73333 =
              let uu____73334 =
                let uu____73339 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73339, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73334  in
            ([[l_imp_a_b]], [aa; bb], uu____73333)  in
          FStar_SMTEncoding_Term.mkForall uu____73321 uu____73322  in
        (uu____73320, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73312  in
    [uu____73311]  in
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
    let uu____73423 =
      let uu____73424 =
        let uu____73432 =
          let uu____73433 = FStar_TypeChecker_Env.get_range env  in
          let uu____73434 =
            let uu____73445 =
              let uu____73446 =
                let uu____73451 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73451, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73446  in
            ([[l_iff_a_b]], [aa; bb], uu____73445)  in
          FStar_SMTEncoding_Term.mkForall uu____73433 uu____73434  in
        (uu____73432, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73424  in
    [uu____73423]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73522 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73522  in
    let uu____73527 =
      let uu____73528 =
        let uu____73536 =
          let uu____73537 = FStar_TypeChecker_Env.get_range env  in
          let uu____73538 =
            let uu____73549 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73549)  in
          FStar_SMTEncoding_Term.mkForall uu____73537 uu____73538  in
        (uu____73536, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73528  in
    [uu____73527]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73602 =
      let uu____73603 =
        let uu____73611 =
          let uu____73612 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73612 range_ty  in
        let uu____73613 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73611, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73613)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73603  in
    [uu____73602]  in
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
        let uu____73659 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73659 x1 t  in
      let uu____73661 = FStar_TypeChecker_Env.get_range env  in
      let uu____73662 =
        let uu____73673 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73673)  in
      FStar_SMTEncoding_Term.mkForall uu____73661 uu____73662  in
    let uu____73698 =
      let uu____73699 =
        let uu____73707 =
          let uu____73708 = FStar_TypeChecker_Env.get_range env  in
          let uu____73709 =
            let uu____73720 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73720)  in
          FStar_SMTEncoding_Term.mkForall uu____73708 uu____73709  in
        (uu____73707,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73699  in
    [uu____73698]  in
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
    let uu____73781 =
      let uu____73782 =
        let uu____73790 =
          let uu____73791 = FStar_TypeChecker_Env.get_range env  in
          let uu____73792 =
            let uu____73808 =
              let uu____73809 =
                let uu____73814 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73815 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73814, uu____73815)  in
              FStar_SMTEncoding_Util.mkAnd uu____73809  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73808)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73791 uu____73792  in
        (uu____73790,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73782  in
    [uu____73781]  in
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
          let uu____74373 =
            FStar_Util.find_opt
              (fun uu____74411  ->
                 match uu____74411 with
                 | (l,uu____74427) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74373 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74470,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74531 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74531 with
        | (form,decls) ->
            let uu____74540 =
              let uu____74543 =
                let uu____74546 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74546]  in
              FStar_All.pipe_right uu____74543
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74540
  
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
              let uu____74605 =
                ((let uu____74609 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74609) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74605
              then
                let arg_sorts =
                  let uu____74621 =
                    let uu____74622 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74622.FStar_Syntax_Syntax.n  in
                  match uu____74621 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74628) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74666  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74673 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74675 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74675 with
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
                    let uu____74707 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74707, env1)
              else
                (let uu____74712 = prims.is lid  in
                 if uu____74712
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74721 = prims.mk lid vname  in
                   match uu____74721 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74745 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74745, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74754 =
                      let uu____74773 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74773 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74801 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74801
                            then
                              let uu____74806 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___934_74809 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___934_74809.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___934_74809.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___934_74809.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___934_74809.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___934_74809.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___934_74809.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___934_74809.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___934_74809.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___934_74809.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___934_74809.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___934_74809.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___934_74809.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___934_74809.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___934_74809.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___934_74809.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___934_74809.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___934_74809.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___934_74809.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___934_74809.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___934_74809.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___934_74809.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___934_74809.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___934_74809.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___934_74809.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___934_74809.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___934_74809.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___934_74809.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___934_74809.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___934_74809.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___934_74809.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___934_74809.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___934_74809.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___934_74809.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___934_74809.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___934_74809.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___934_74809.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___934_74809.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___934_74809.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___934_74809.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___934_74809.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___934_74809.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___934_74809.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74806
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74832 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74832)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74754 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74938  ->
                                  match uu___639_74938 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74942 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74942 with
                                       | (uu____74975,xxv) ->
                                           let xx =
                                             let uu____75014 =
                                               let uu____75015 =
                                                 let uu____75021 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75021,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75015
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75014
                                              in
                                           let uu____75024 =
                                             let uu____75025 =
                                               let uu____75033 =
                                                 let uu____75034 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75035 =
                                                   let uu____75046 =
                                                     let uu____75047 =
                                                       let uu____75052 =
                                                         let uu____75053 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75053
                                                          in
                                                       (vapp, uu____75052)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75047
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75046)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75034 uu____75035
                                                  in
                                               (uu____75033,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75025
                                              in
                                           [uu____75024])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75068 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75068 with
                                       | (uu____75101,xxv) ->
                                           let xx =
                                             let uu____75140 =
                                               let uu____75141 =
                                                 let uu____75147 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75147,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75141
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75140
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
                                           let uu____75158 =
                                             let uu____75159 =
                                               let uu____75167 =
                                                 let uu____75168 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75169 =
                                                   let uu____75180 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75180)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75168 uu____75169
                                                  in
                                               (uu____75167,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75159
                                              in
                                           [uu____75158])
                                  | uu____75193 -> []))
                           in
                        let uu____75194 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75194 with
                         | (vars,guards,env',decls1,uu____75219) ->
                             let uu____75232 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75245 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75245, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75249 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75249 with
                                    | (g,ds) ->
                                        let uu____75262 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75262,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75232 with
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
                                  let should_thunk uu____75285 =
                                    let is_type1 t =
                                      let uu____75293 =
                                        let uu____75294 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75294.FStar_Syntax_Syntax.n  in
                                      match uu____75293 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75298 -> true
                                      | uu____75300 -> false  in
                                    let is_squash1 t =
                                      let uu____75309 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75309 with
                                      | (head1,uu____75328) ->
                                          let uu____75353 =
                                            let uu____75354 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75354.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75353 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75359;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75360;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75362;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75363;_};_},uu____75364)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75372 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75377 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75377))
                                       &&
                                       (let uu____75383 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75383))
                                      &&
                                      (let uu____75386 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75386)
                                     in
                                  let uu____75388 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75447 -> (false, vars)  in
                                  (match uu____75388 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75497 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75497 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75529 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75538 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75538
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75549 ->
                                                  let uu____75558 =
                                                    let uu____75566 =
                                                      get_vtok ()  in
                                                    (uu____75566, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75558
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75573 =
                                                let uu____75581 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75581)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75573
                                               in
                                            let uu____75595 =
                                              let vname_decl =
                                                let uu____75603 =
                                                  let uu____75615 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75615,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75603
                                                 in
                                              let uu____75626 =
                                                let env2 =
                                                  let uu___1029_75632 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1029_75632.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75633 =
                                                  let uu____75635 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75635
                                                   in
                                                if uu____75633
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75626 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75652 =
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
                                                        let uu____75678 =
                                                          let uu____75681 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75681
                                                           in
                                                        let uu____75688 =
                                                          let uu____75689 =
                                                            let uu____75692 =
                                                              let uu____75693
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75693
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75697  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75697)
                                                              uu____75692
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75689
                                                           in
                                                        (uu____75678,
                                                          uu____75688)
                                                    | uu____75700 when
                                                        thunked ->
                                                        let uu____75711 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75711
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75726
                                                                 =
                                                                 let uu____75734
                                                                   =
                                                                   let uu____75737
                                                                    =
                                                                    let uu____75740
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75740]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75737
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75734)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75726
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75748
                                                               =
                                                               let uu____75756
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75756,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75748
                                                              in
                                                           let uu____75761 =
                                                             let uu____75764
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75764
                                                              in
                                                           (uu____75761,
                                                             env1))
                                                    | uu____75773 ->
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
                                                          let uu____75797 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75798 =
                                                            let uu____75809 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75809)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75797
                                                            uu____75798
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75819 =
                                                            let uu____75827 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75827,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75819
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
                                                            let uu____75838 =
                                                              let uu____75839
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75839]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75838
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75866 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75867 =
                                                              let uu____75878
                                                                =
                                                                let uu____75879
                                                                  =
                                                                  let uu____75884
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75885
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75884,
                                                                    uu____75885)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75879
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75878)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75866
                                                              uu____75867
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75914 =
                                                          let uu____75917 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75917
                                                           in
                                                        (uu____75914, env1)
                                                     in
                                                  (match uu____75652 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75938 =
                                                         let uu____75941 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75941
                                                           tok_decl
                                                          in
                                                       (uu____75938, env2))
                                               in
                                            (match uu____75595 with
                                             | (decls2,env2) ->
                                                 let uu____75960 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75970 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75970 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75985 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75985, decls)
                                                    in
                                                 (match uu____75960 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____76000 =
                                                          let uu____76008 =
                                                            let uu____76009 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76010 =
                                                              let uu____76021
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____76021)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____76009
                                                              uu____76010
                                                             in
                                                          (uu____76008,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____76000
                                                         in
                                                      let freshness =
                                                        let uu____76037 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____76037
                                                        then
                                                          let uu____76045 =
                                                            let uu____76046 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76047 =
                                                              let uu____76060
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76067
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76060,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76067)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____76046
                                                              uu____76047
                                                             in
                                                          let uu____76073 =
                                                            let uu____76076 =
                                                              let uu____76077
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76077
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76076]  in
                                                          uu____76045 ::
                                                            uu____76073
                                                        else []  in
                                                      let g =
                                                        let uu____76083 =
                                                          let uu____76086 =
                                                            let uu____76089 =
                                                              let uu____76092
                                                                =
                                                                let uu____76095
                                                                  =
                                                                  let uu____76098
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76098
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76095
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76092
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76089
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76086
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76083
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
          let uu____76138 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76138 with
          | FStar_Pervasives_Native.None  ->
              let uu____76149 = encode_free_var false env x t t_norm []  in
              (match uu____76149 with
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
            let uu____76212 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76212 with
            | (decls,env1) ->
                let uu____76223 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76223
                then
                  let uu____76230 =
                    let uu____76231 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76231  in
                  (uu____76230, env1)
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
             (fun uu____76287  ->
                fun lb  ->
                  match uu____76287 with
                  | (decls,env1) ->
                      let uu____76307 =
                        let uu____76312 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76312
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76307 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76341 = FStar_Syntax_Util.head_and_args t  in
    match uu____76341 with
    | (hd1,args) ->
        let uu____76385 =
          let uu____76386 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76386.FStar_Syntax_Syntax.n  in
        (match uu____76385 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76392,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76416 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76427 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1116_76435 = en  in
    let uu____76436 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1116_76435.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1116_76435.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1116_76435.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1116_76435.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1116_76435.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1116_76435.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1116_76435.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1116_76435.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1116_76435.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1116_76435.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76436
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76466  ->
      fun quals  ->
        match uu____76466 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76571 = FStar_Util.first_N nbinders formals  in
              match uu____76571 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76668  ->
                         fun uu____76669  ->
                           match (uu____76668, uu____76669) with
                           | ((formal,uu____76695),(binder,uu____76697)) ->
                               let uu____76718 =
                                 let uu____76725 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76725)  in
                               FStar_Syntax_Syntax.NT uu____76718) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76739 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76780  ->
                              match uu____76780 with
                              | (x,i) ->
                                  let uu____76799 =
                                    let uu___1142_76800 = x  in
                                    let uu____76801 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1142_76800.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1142_76800.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76801
                                    }  in
                                  (uu____76799, i)))
                       in
                    FStar_All.pipe_right uu____76739
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76825 =
                      let uu____76830 = FStar_Syntax_Subst.compress body  in
                      let uu____76831 =
                        let uu____76832 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76832
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76830
                        uu____76831
                       in
                    uu____76825 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1149_76881 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1149_76881.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1149_76881.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1149_76881.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1149_76881.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1149_76881.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1149_76881.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1149_76881.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1149_76881.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1149_76881.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1149_76881.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1149_76881.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1149_76881.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1149_76881.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1149_76881.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1149_76881.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1149_76881.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1149_76881.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1149_76881.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1149_76881.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1149_76881.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1149_76881.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1149_76881.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1149_76881.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1149_76881.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1149_76881.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1149_76881.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1149_76881.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1149_76881.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1149_76881.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1149_76881.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1149_76881.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1149_76881.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1149_76881.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1149_76881.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1149_76881.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1149_76881.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1149_76881.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1149_76881.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1149_76881.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1149_76881.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1149_76881.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1149_76881.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76953  ->
                       fun uu____76954  ->
                         match (uu____76953, uu____76954) with
                         | ((x,uu____76980),(b,uu____76982)) ->
                             let uu____77003 =
                               let uu____77010 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____77010)  in
                             FStar_Syntax_Syntax.NT uu____77003) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____77035 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____77035
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77064 ->
                    let uu____77071 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77071
                | uu____77072 when Prims.op_Negation norm1 ->
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
                | uu____77075 ->
                    let uu____77076 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77076)
                 in
              let aux t1 e1 =
                let uu____77118 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77118 with
                | (binders,body,lopt) ->
                    let uu____77150 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77166 -> arrow_formals_comp_norm false t1  in
                    (match uu____77150 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77200 =
                           if nformals < nbinders
                           then
                             let uu____77234 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77234 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77314 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77314)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77344 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77344 with
                                | (binders1,body1) ->
                                    let uu____77397 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77397))
                             else
                               (let uu____77410 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77410))
                            in
                         (match uu____77200 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77470 = aux t e  in
              match uu____77470 with
              | (binders,body,comp) ->
                  let uu____77516 =
                    let uu____77527 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77527
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77542 = aux comp1 body1  in
                      match uu____77542 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77516 with
                   | (binders1,body1,comp1) ->
                       let uu____77625 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77625, comp1))
               in
            (try
               (fun uu___1219_77652  ->
                  match () with
                  | () ->
                      let uu____77659 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77659
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77675 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77738  ->
                                   fun lb  ->
                                     match uu____77738 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77793 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77793
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77799 =
                                             let uu____77808 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77808
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77799 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77675 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77949;
                                    FStar_Syntax_Syntax.lbeff = uu____77950;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77952;
                                    FStar_Syntax_Syntax.lbpos = uu____77953;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77977 =
                                     let uu____77984 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77984 with
                                     | (tcenv',uu____78000,e_t) ->
                                         let uu____78006 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____78017 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____78006 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1282_78034 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1282_78034.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77977 with
                                    | (env',e1,t_norm1) ->
                                        let uu____78044 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____78044 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78064 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78064
                                               then
                                                 let uu____78069 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78072 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78069 uu____78072
                                               else ());
                                              (let uu____78077 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78077 with
                                               | (vars,_guards,env'1,binder_decls,uu____78104)
                                                   ->
                                                   let uu____78117 =
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
                                                         let uu____78134 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78134
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78156 =
                                                          let uu____78157 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78158 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78157 fvb
                                                            uu____78158
                                                           in
                                                        (vars, uu____78156))
                                                      in
                                                   (match uu____78117 with
                                                    | (vars1,app) ->
                                                        let uu____78169 =
                                                          let is_logical =
                                                            let uu____78182 =
                                                              let uu____78183
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78183.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78182
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78189 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78193 =
                                                              let uu____78194
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78194
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78193
                                                              (fun lid  ->
                                                                 let uu____78203
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78203
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78204 =
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
                                                          if uu____78204
                                                          then
                                                            let uu____78220 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78221 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78220,
                                                              uu____78221)
                                                          else
                                                            (let uu____78232
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78232))
                                                           in
                                                        (match uu____78169
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78256
                                                                 =
                                                                 let uu____78264
                                                                   =
                                                                   let uu____78265
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78266
                                                                    =
                                                                    let uu____78277
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78277)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78265
                                                                    uu____78266
                                                                    in
                                                                 let uu____78286
                                                                   =
                                                                   let uu____78287
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78287
                                                                    in
                                                                 (uu____78264,
                                                                   uu____78286,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78256
                                                                in
                                                             let uu____78293
                                                               =
                                                               let uu____78296
                                                                 =
                                                                 let uu____78299
                                                                   =
                                                                   let uu____78302
                                                                    =
                                                                    let uu____78305
                                                                    =
                                                                    let uu____78308
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78308
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78305
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78302
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78299
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78296
                                                                in
                                                             (uu____78293,
                                                               env2)))))))
                               | uu____78317 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78377 =
                                   let uu____78383 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78383,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78377  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78389 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78442  ->
                                         fun fvb  ->
                                           match uu____78442 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78497 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78497
                                                  in
                                               let gtok =
                                                 let uu____78501 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78501
                                                  in
                                               let env4 =
                                                 let uu____78504 =
                                                   let uu____78507 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78513  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78513) uu____78507
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78504
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78389 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78633
                                     t_norm uu____78635 =
                                     match (uu____78633, uu____78635) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78665;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78666;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78668;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78669;_})
                                         ->
                                         let uu____78696 =
                                           let uu____78703 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78703 with
                                           | (tcenv',uu____78719,e_t) ->
                                               let uu____78725 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78736 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78725 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1369_78753 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1369_78753.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78696 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78766 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78766
                                                then
                                                  let uu____78771 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78773 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78775 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78771 uu____78773
                                                    uu____78775
                                                else ());
                                               (let uu____78780 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78780 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78807 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78807 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78829 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78829
                                                           then
                                                             let uu____78834
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78836
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78839
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78841
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78834
                                                               uu____78836
                                                               uu____78839
                                                               uu____78841
                                                           else ());
                                                          (let uu____78846 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78846
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78875)
                                                               ->
                                                               let uu____78888
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78901
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78901,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78905
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78905
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78918
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78918,
                                                                    decls0))
                                                                  in
                                                               (match uu____78888
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
                                                                    let uu____78939
                                                                    =
                                                                    let uu____78951
                                                                    =
                                                                    let uu____78954
                                                                    =
                                                                    let uu____78957
                                                                    =
                                                                    let uu____78960
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78960
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78957
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78954
                                                                     in
                                                                    (g,
                                                                    uu____78951,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78939
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
                                                                    let uu____78990
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78990
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
                                                                    let uu____79005
                                                                    =
                                                                    let uu____79008
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____79008
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79005
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____79014
                                                                    =
                                                                    let uu____79017
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____79017
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79014
                                                                     in
                                                                    let uu____79022
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____79022
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____79038
                                                                    =
                                                                    let uu____79046
                                                                    =
                                                                    let uu____79047
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79048
                                                                    =
                                                                    let uu____79064
                                                                    =
                                                                    let uu____79065
                                                                    =
                                                                    let uu____79070
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79070)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79065
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79064)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79047
                                                                    uu____79048
                                                                     in
                                                                    let uu____79084
                                                                    =
                                                                    let uu____79085
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79085
                                                                     in
                                                                    (uu____79046,
                                                                    uu____79084,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79038
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79092
                                                                    =
                                                                    let uu____79100
                                                                    =
                                                                    let uu____79101
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79102
                                                                    =
                                                                    let uu____79113
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79113)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79101
                                                                    uu____79102
                                                                     in
                                                                    (uu____79100,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79092
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79127
                                                                    =
                                                                    let uu____79135
                                                                    =
                                                                    let uu____79136
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79137
                                                                    =
                                                                    let uu____79148
                                                                    =
                                                                    let uu____79149
                                                                    =
                                                                    let uu____79154
                                                                    =
                                                                    let uu____79155
                                                                    =
                                                                    let uu____79158
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79158
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79155
                                                                     in
                                                                    (gsapp,
                                                                    uu____79154)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79149
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79148)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79136
                                                                    uu____79137
                                                                     in
                                                                    (uu____79135,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79127
                                                                     in
                                                                    let uu____79172
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
                                                                    let uu____79184
                                                                    =
                                                                    let uu____79185
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79185
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79184
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79187
                                                                    =
                                                                    let uu____79195
                                                                    =
                                                                    let uu____79196
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79197
                                                                    =
                                                                    let uu____79208
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79208)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79196
                                                                    uu____79197
                                                                     in
                                                                    (uu____79195,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79187
                                                                     in
                                                                    let uu____79221
                                                                    =
                                                                    let uu____79230
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79230
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79245
                                                                    =
                                                                    let uu____79248
                                                                    =
                                                                    let uu____79249
                                                                    =
                                                                    let uu____79257
                                                                    =
                                                                    let uu____79258
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79259
                                                                    =
                                                                    let uu____79270
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79270)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79258
                                                                    uu____79259
                                                                     in
                                                                    (uu____79257,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79249
                                                                     in
                                                                    [uu____79248]
                                                                     in
                                                                    (d3,
                                                                    uu____79245)
                                                                     in
                                                                    match uu____79221
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79172
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79327
                                                                    =
                                                                    let uu____79330
                                                                    =
                                                                    let uu____79333
                                                                    =
                                                                    let uu____79336
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79336
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79333
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79330
                                                                     in
                                                                    let uu____79343
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79327,
                                                                    uu____79343,
                                                                    env02))))))))))
                                      in
                                   let uu____79348 =
                                     let uu____79361 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79424  ->
                                          fun uu____79425  ->
                                            match (uu____79424, uu____79425)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79550 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79550 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79361
                                      in
                                   (match uu____79348 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79617 =
                                          let isDeclFun uu___640_79634 =
                                            match uu___640_79634 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79636 -> true
                                            | uu____79649 -> false  in
                                          let uu____79651 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79651
                                            (fun decls3  ->
                                               let uu____79681 =
                                                 FStar_List.fold_left
                                                   (fun uu____79712  ->
                                                      fun elt  ->
                                                        match uu____79712
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79753 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79753
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79781
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79781
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
                                                                    let uu___1462_79819
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1462_79819.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1462_79819.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1462_79819.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79681 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79851 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79851, elts, rest))
                                           in
                                        (match uu____79617 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79880 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79886  ->
                                        match uu___641_79886 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79889 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79897 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79897)))
                                in
                             if uu____79880
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1479_79919  ->
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
                   let uu____79958 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79958
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79977 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79977, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____80033 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____80033 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____80039 = encode_sigelt' env se  in
      match uu____80039 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80051 =
                  let uu____80054 =
                    let uu____80055 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80055  in
                  [uu____80054]  in
                FStar_All.pipe_right uu____80051
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80060 ->
                let uu____80061 =
                  let uu____80064 =
                    let uu____80067 =
                      let uu____80068 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80068  in
                    [uu____80067]  in
                  FStar_All.pipe_right uu____80064
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80075 =
                  let uu____80078 =
                    let uu____80081 =
                      let uu____80084 =
                        let uu____80085 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80085  in
                      [uu____80084]  in
                    FStar_All.pipe_right uu____80081
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80078  in
                FStar_List.append uu____80061 uu____80075
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80099 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80099
       then
         let uu____80104 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80104
       else ());
      (let is_opaque_to_smt t =
         let uu____80116 =
           let uu____80117 = FStar_Syntax_Subst.compress t  in
           uu____80117.FStar_Syntax_Syntax.n  in
         match uu____80116 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80122)) -> s = "opaque_to_smt"
         | uu____80127 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80136 =
           let uu____80137 = FStar_Syntax_Subst.compress t  in
           uu____80137.FStar_Syntax_Syntax.n  in
         match uu____80136 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80142)) -> s = "uninterpreted_by_smt"
         | uu____80147 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80153 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80159 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80171 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80172 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80173 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80186 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80188 =
             let uu____80190 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80190  in
           if uu____80188
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80219 ->
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
                  let uu____80252 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____80252  in
                let uu____80253 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80253 with
                | (formals,uu____80273) ->
                    let arity = FStar_List.length formals  in
                    let uu____80297 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80297 with
                     | (aname,atok,env2) ->
                         let uu____80319 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____80319 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80335 =
                                  let uu____80336 =
                                    let uu____80348 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80368  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80348,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80336
                                   in
                                [uu____80335;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80385 =
                                let aux uu____80431 uu____80432 =
                                  match (uu____80431, uu____80432) with
                                  | ((bv,uu____80476),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80508 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80508 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80531 =
                                             let uu____80534 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80534 :: acc_sorts  in
                                           (env4, uu____80531, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80385 with
                               | (uu____80566,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80582 =
                                       let uu____80590 =
                                         let uu____80591 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80592 =
                                           let uu____80603 =
                                             let uu____80604 =
                                               let uu____80609 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80609)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80604
                                              in
                                           ([[app]], xs_sorts, uu____80603)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80591 uu____80592
                                          in
                                       (uu____80590,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80582
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80624 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80624
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80627 =
                                       let uu____80635 =
                                         let uu____80636 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80637 =
                                           let uu____80648 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80648)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80636 uu____80637
                                          in
                                       (uu____80635,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80627
                                      in
                                   let uu____80661 =
                                     let uu____80664 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80664  in
                                   (env2, uu____80661))))
                 in
              let uu____80673 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80673 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80699,uu____80700)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80701 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80701 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80723,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80730 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80736  ->
                       match uu___642_80736 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80739 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80745 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80748 -> false))
                in
             Prims.op_Negation uu____80730  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80758 =
                let uu____80763 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80763 env fv t quals  in
              match uu____80758 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80777 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80777  in
                  let uu____80780 =
                    let uu____80781 =
                      let uu____80784 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80784
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80781  in
                  (uu____80780, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80794 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80794 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1616_80806 = env  in
                  let uu____80807 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1616_80806.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1616_80806.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1616_80806.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80807;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1616_80806.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1616_80806.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1616_80806.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1616_80806.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1616_80806.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1616_80806.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1616_80806.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____80809 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80809 with
                 | (f3,decls) ->
                     let g =
                       let uu____80823 =
                         let uu____80826 =
                           let uu____80827 =
                             let uu____80835 =
                               let uu____80836 =
                                 let uu____80838 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80838
                                  in
                               FStar_Pervasives_Native.Some uu____80836  in
                             let uu____80842 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80835, uu____80842)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80827  in
                         [uu____80826]  in
                       FStar_All.pipe_right uu____80823
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80851) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80865 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80887 =
                        let uu____80890 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80890.FStar_Syntax_Syntax.fv_name  in
                      uu____80887.FStar_Syntax_Syntax.v  in
                    let uu____80891 =
                      let uu____80893 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80893  in
                    if uu____80891
                    then
                      let val_decl =
                        let uu___1633_80925 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1633_80925.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1633_80925.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1633_80925.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80926 = encode_sigelt' env1 val_decl  in
                      match uu____80926 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80865 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80962,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80964;
                           FStar_Syntax_Syntax.lbtyp = uu____80965;
                           FStar_Syntax_Syntax.lbeff = uu____80966;
                           FStar_Syntax_Syntax.lbdef = uu____80967;
                           FStar_Syntax_Syntax.lbattrs = uu____80968;
                           FStar_Syntax_Syntax.lbpos = uu____80969;_}::[]),uu____80970)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80989 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80989 with
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
                  let uu____81027 =
                    let uu____81030 =
                      let uu____81031 =
                        let uu____81039 =
                          let uu____81040 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____81041 =
                            let uu____81052 =
                              let uu____81053 =
                                let uu____81058 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81058)  in
                              FStar_SMTEncoding_Util.mkEq uu____81053  in
                            ([[b2t_x]], [xx], uu____81052)  in
                          FStar_SMTEncoding_Term.mkForall uu____81040
                            uu____81041
                           in
                        (uu____81039,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____81031  in
                    [uu____81030]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____81027
                   in
                let uu____81096 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81096, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81099,uu____81100) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81110  ->
                   match uu___643_81110 with
                   | FStar_Syntax_Syntax.Discriminator uu____81112 -> true
                   | uu____81114 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81116,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81128 =
                      let uu____81130 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81130.FStar_Ident.idText  in
                    uu____81128 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81137  ->
                      match uu___644_81137 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81140 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81143) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81157  ->
                   match uu___645_81157 with
                   | FStar_Syntax_Syntax.Projector uu____81159 -> true
                   | uu____81165 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81169 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81169 with
            | FStar_Pervasives_Native.Some uu____81176 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1698_81178 = se  in
                  let uu____81179 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81179;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1698_81178.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1698_81178.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1698_81178.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81182) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1710_81203 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1710_81203.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1710_81203.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1710_81203.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1710_81203.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1710_81203.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81208) ->
           let uu____81217 = encode_sigelts env ses  in
           (match uu____81217 with
            | (g,env1) ->
                let uu____81228 =
                  FStar_List.fold_left
                    (fun uu____81252  ->
                       fun elt  ->
                         match uu____81252 with
                         | (g',inversions) ->
                             let uu____81280 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81303  ->
                                       match uu___646_81303 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81305;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81306;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81307;_}
                                           -> false
                                       | uu____81314 -> true))
                                in
                             (match uu____81280 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1736_81339 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1736_81339.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1736_81339.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1736_81339.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81228 with
                 | (g',inversions) ->
                     let uu____81358 =
                       FStar_List.fold_left
                         (fun uu____81389  ->
                            fun elt  ->
                              match uu____81389 with
                              | (decls,elts,rest) ->
                                  let uu____81430 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81439  ->
                                            match uu___647_81439 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81441 -> true
                                            | uu____81454 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81430
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81477 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81498  ->
                                               match uu___648_81498 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81500 -> true
                                               | uu____81513 -> false))
                                        in
                                     match uu____81477 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1758_81544 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1758_81544.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1758_81544.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1758_81544.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81358 with
                      | (decls,elts,rest) ->
                          let uu____81570 =
                            let uu____81571 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81578 =
                              let uu____81581 =
                                let uu____81584 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81584  in
                              FStar_List.append elts uu____81581  in
                            FStar_List.append uu____81571 uu____81578  in
                          (uu____81570, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81595,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81608 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81608 with
             | (usubst,uvs) ->
                 let uu____81628 =
                   let uu____81635 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81636 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81637 =
                     let uu____81638 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81638 k  in
                   (uu____81635, uu____81636, uu____81637)  in
                 (match uu____81628 with
                  | (env1,tps1,k1) ->
                      let uu____81651 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81651 with
                       | (tps2,k2) ->
                           let uu____81659 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81659 with
                            | (uu____81675,k3) ->
                                let uu____81697 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81697 with
                                 | (tps3,env_tps,uu____81709,us) ->
                                     let u_k =
                                       let uu____81712 =
                                         let uu____81713 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81714 =
                                           let uu____81719 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81721 =
                                             let uu____81722 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81722
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81719 uu____81721
                                            in
                                         uu____81714
                                           FStar_Pervasives_Native.None
                                           uu____81713
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81712 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81740) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81746,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81749) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81757,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81764) ->
                                           let uu____81765 =
                                             let uu____81767 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81767
                                              in
                                           failwith uu____81765
                                       | (uu____81771,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81772 =
                                             let uu____81774 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81774
                                              in
                                           failwith uu____81772
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81778,uu____81779) ->
                                           let uu____81788 =
                                             let uu____81790 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81790
                                              in
                                           failwith uu____81788
                                       | (uu____81794,FStar_Syntax_Syntax.U_unif
                                          uu____81795) ->
                                           let uu____81804 =
                                             let uu____81806 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81806
                                              in
                                           failwith uu____81804
                                       | uu____81810 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81823 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81823 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81841 = u_leq_u_k u_tp  in
                                       if uu____81841
                                       then true
                                       else
                                         (let uu____81848 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81848 with
                                          | (formals,uu____81865) ->
                                              let uu____81886 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81886 with
                                               | (uu____81896,uu____81897,uu____81898,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81909 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81909
             then
               let uu____81914 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81914
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81934  ->
                       match uu___649_81934 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81938 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81951 = c  in
                 match uu____81951 with
                 | (name,args,uu____81956,uu____81957,uu____81958) ->
                     let uu____81969 =
                       let uu____81970 =
                         let uu____81982 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____82009  ->
                                   match uu____82009 with
                                   | (uu____82018,sort,uu____82020) -> sort))
                            in
                         (name, uu____81982,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81970  in
                     [uu____81969]
               else
                 (let uu____82031 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____82031 c)
                in
             let inversion_axioms tapp vars =
               let uu____82049 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____82057 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____82057 FStar_Option.isNone))
                  in
               if uu____82049
               then []
               else
                 (let uu____82092 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82092 with
                  | (xxsym,xx) ->
                      let uu____82105 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82144  ->
                                fun l  ->
                                  match uu____82144 with
                                  | (out,decls) ->
                                      let uu____82164 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82164 with
                                       | (uu____82175,data_t) ->
                                           let uu____82177 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82177 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82221 =
                                                    let uu____82222 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82222.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82221 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82225,indices)
                                                      -> indices
                                                  | uu____82251 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82281  ->
                                                            match uu____82281
                                                            with
                                                            | (x,uu____82289)
                                                                ->
                                                                let uu____82294
                                                                  =
                                                                  let uu____82295
                                                                    =
                                                                    let uu____82303
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82303,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82295
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82294)
                                                       env)
                                                   in
                                                let uu____82308 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82308 with
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
                                                                  let uu____82343
                                                                    =
                                                                    let uu____82348
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82348,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82343)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82351 =
                                                         let uu____82352 =
                                                           let uu____82357 =
                                                             let uu____82358
                                                               =
                                                               let uu____82363
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82364
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82363,
                                                                 uu____82364)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82358
                                                              in
                                                           (out, uu____82357)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82352
                                                          in
                                                       (uu____82351,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82105 with
                       | (data_ax,decls) ->
                           let uu____82379 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82379 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82396 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82396 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82403 =
                                    let uu____82411 =
                                      let uu____82412 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82413 =
                                        let uu____82424 =
                                          let uu____82425 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82427 =
                                            let uu____82430 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82430 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82425 uu____82427
                                           in
                                        let uu____82432 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82424,
                                          uu____82432)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82412 uu____82413
                                       in
                                    let uu____82441 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82411,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82441)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82403
                                   in
                                let uu____82447 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82447)))
                in
             let uu____82454 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____82476 ->
                     let uu____82477 =
                       let uu____82484 =
                         let uu____82485 =
                           let uu____82500 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____82500)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____82485  in
                       FStar_Syntax_Syntax.mk uu____82484  in
                     uu____82477 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____82454 with
             | (formals,res) ->
                 let uu____82540 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____82540 with
                  | (vars,guards,env',binder_decls,uu____82565) ->
                      let arity = FStar_List.length vars  in
                      let uu____82579 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____82579 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____82605 =
                               let uu____82613 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____82613)  in
                             FStar_SMTEncoding_Util.mkApp uu____82605  in
                           let uu____82619 =
                             let tname_decl =
                               let uu____82629 =
                                 let uu____82630 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____82649 =
                                             let uu____82651 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____82651
                                              in
                                           let uu____82653 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____82649, uu____82653, false)))
                                    in
                                 let uu____82657 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____82630,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____82657, false)
                                  in
                               constructor_or_logic_type_decl uu____82629  in
                             let uu____82665 =
                               match vars with
                               | [] ->
                                   let uu____82678 =
                                     let uu____82679 =
                                       let uu____82682 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _82688  ->
                                            FStar_Pervasives_Native.Some
                                              _82688) uu____82682
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____82679
                                      in
                                   ([], uu____82678)
                               | uu____82691 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____82701 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____82701
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____82717 =
                                       let uu____82725 =
                                         let uu____82726 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____82727 =
                                           let uu____82743 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____82743)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____82726 uu____82727
                                          in
                                       (uu____82725,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____82717
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____82665 with
                             | (tok_decls,env2) ->
                                 let uu____82770 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____82770
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____82619 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____82798 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____82798 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____82820 =
                                            let uu____82821 =
                                              let uu____82829 =
                                                let uu____82830 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____82830
                                                 in
                                              (uu____82829,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____82821
                                             in
                                          [uu____82820]
                                        else []  in
                                      let uu____82838 =
                                        let uu____82841 =
                                          let uu____82844 =
                                            let uu____82847 =
                                              let uu____82848 =
                                                let uu____82856 =
                                                  let uu____82857 =
                                                    FStar_Ident.range_of_lid
                                                      t
                                                     in
                                                  let uu____82858 =
                                                    let uu____82869 =
                                                      FStar_SMTEncoding_Util.mkImp
                                                        (guard, k1)
                                                       in
                                                    ([[tapp]], vars,
                                                      uu____82869)
                                                     in
                                                  FStar_SMTEncoding_Term.mkForall
                                                    uu____82857 uu____82858
                                                   in
                                                (uu____82856,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____82848
                                               in
                                            [uu____82847]  in
                                          FStar_List.append karr uu____82844
                                           in
                                        FStar_All.pipe_right uu____82841
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____82838
                                   in
                                let aux =
                                  let uu____82888 =
                                    let uu____82891 =
                                      inversion_axioms tapp vars  in
                                    let uu____82894 =
                                      let uu____82897 =
                                        let uu____82900 =
                                          let uu____82901 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____82901 env2 tapp
                                            vars
                                           in
                                        [uu____82900]  in
                                      FStar_All.pipe_right uu____82897
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____82891 uu____82894
                                     in
                                  FStar_List.append kindingAx uu____82888  in
                                let g =
                                  let uu____82909 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____82909
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82917,uu____82918,uu____82919,uu____82920,uu____82921)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82929,t,uu____82931,n_tps,uu____82933) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____82944 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____82944 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82992 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82992 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____83016 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____83016 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____83036 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____83036 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83115 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83115,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83122 =
                                   let uu____83123 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83123, true)
                                    in
                                 let uu____83131 =
                                   let uu____83138 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83138
                                    in
                                 FStar_All.pipe_right uu____83122 uu____83131
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
                               let uu____83150 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____83150 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83162::uu____83163 ->
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
                                            let uu____83212 =
                                              let uu____83213 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83213]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83212
                                             in
                                          let uu____83239 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83240 =
                                            let uu____83251 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83251)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83239 uu____83240
                                      | uu____83278 -> tok_typing  in
                                    let uu____83289 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83289 with
                                     | (vars',guards',env'',decls_formals,uu____83314)
                                         ->
                                         let uu____83327 =
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
                                         (match uu____83327 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83357 ->
                                                    let uu____83366 =
                                                      let uu____83367 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83367
                                                       in
                                                    [uu____83366]
                                                 in
                                              let encode_elim uu____83383 =
                                                let uu____83384 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83384 with
                                                | (head1,args) ->
                                                    let uu____83435 =
                                                      let uu____83436 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83436.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83435 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83448;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83449;_},uu____83450)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83456 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83456
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
                                                                  | uu____83519
                                                                    ->
                                                                    let uu____83520
                                                                    =
                                                                    let uu____83526
                                                                    =
                                                                    let uu____83528
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83528
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83526)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83520
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83551
                                                                    =
                                                                    let uu____83553
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83553
                                                                     in
                                                                    if
                                                                    uu____83551
                                                                    then
                                                                    let uu____83575
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83575]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83578
                                                                =
                                                                let uu____83592
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83649
                                                                     ->
                                                                    fun
                                                                    uu____83650
                                                                     ->
                                                                    match 
                                                                    (uu____83649,
                                                                    uu____83650)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83761
                                                                    =
                                                                    let uu____83769
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83769
                                                                     in
                                                                    (match uu____83761
                                                                    with
                                                                    | 
                                                                    (uu____83783,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83794
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83794
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83799
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
                                                                  uu____83592
                                                                 in
                                                              (match uu____83578
                                                               with
                                                               | (uu____83820,arg_vars,elim_eqns_or_guards,uu____83823)
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
                                                                    let uu____83850
                                                                    =
                                                                    let uu____83858
                                                                    =
                                                                    let uu____83859
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83860
                                                                    =
                                                                    let uu____83871
                                                                    =
                                                                    let uu____83872
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83872
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83874
                                                                    =
                                                                    let uu____83875
                                                                    =
                                                                    let uu____83880
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83880)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83875
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83871,
                                                                    uu____83874)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83859
                                                                    uu____83860
                                                                     in
                                                                    (uu____83858,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83850
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83895
                                                                    =
                                                                    let uu____83896
                                                                    =
                                                                    let uu____83902
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83902,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83896
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83895
                                                                     in
                                                                    let uu____83905
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83905
                                                                    then
                                                                    let x =
                                                                    let uu____83909
                                                                    =
                                                                    let uu____83915
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83915,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83909
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83920
                                                                    =
                                                                    let uu____83928
                                                                    =
                                                                    let uu____83929
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83930
                                                                    =
                                                                    let uu____83941
                                                                    =
                                                                    let uu____83946
                                                                    =
                                                                    let uu____83949
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83949]
                                                                     in
                                                                    [uu____83946]
                                                                     in
                                                                    let uu____83954
                                                                    =
                                                                    let uu____83955
                                                                    =
                                                                    let uu____83960
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83960,
                                                                    uu____83962)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83955
                                                                     in
                                                                    (uu____83941,
                                                                    [x],
                                                                    uu____83954)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83929
                                                                    uu____83930
                                                                     in
                                                                    let uu____83983
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83928,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83983)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83920
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83994
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
                                                                    (let uu____84017
                                                                    =
                                                                    let uu____84018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84018
                                                                    dapp1  in
                                                                    [uu____84017])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83994
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84025
                                                                    =
                                                                    let uu____84033
                                                                    =
                                                                    let uu____84034
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84035
                                                                    =
                                                                    let uu____84046
                                                                    =
                                                                    let uu____84047
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84047
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84049
                                                                    =
                                                                    let uu____84050
                                                                    =
                                                                    let uu____84055
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84055)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84050
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84046,
                                                                    uu____84049)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84034
                                                                    uu____84035
                                                                     in
                                                                    (uu____84033,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84025)
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
                                                         let uu____84074 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84074
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
                                                                  | uu____84137
                                                                    ->
                                                                    let uu____84138
                                                                    =
                                                                    let uu____84144
                                                                    =
                                                                    let uu____84146
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84146
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84144)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84138
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84169
                                                                    =
                                                                    let uu____84171
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84171
                                                                     in
                                                                    if
                                                                    uu____84169
                                                                    then
                                                                    let uu____84193
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84193]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84196
                                                                =
                                                                let uu____84210
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84267
                                                                     ->
                                                                    fun
                                                                    uu____84268
                                                                     ->
                                                                    match 
                                                                    (uu____84267,
                                                                    uu____84268)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84379
                                                                    =
                                                                    let uu____84387
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84387
                                                                     in
                                                                    (match uu____84379
                                                                    with
                                                                    | 
                                                                    (uu____84401,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84412
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84412
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84417
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84417
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
                                                                  uu____84210
                                                                 in
                                                              (match uu____84196
                                                               with
                                                               | (uu____84438,arg_vars,elim_eqns_or_guards,uu____84441)
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
                                                                    let uu____84468
                                                                    =
                                                                    let uu____84476
                                                                    =
                                                                    let uu____84477
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84478
                                                                    =
                                                                    let uu____84489
                                                                    =
                                                                    let uu____84490
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84490
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84492
                                                                    =
                                                                    let uu____84493
                                                                    =
                                                                    let uu____84498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84498)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84493
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84489,
                                                                    uu____84492)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84477
                                                                    uu____84478
                                                                     in
                                                                    (uu____84476,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84468
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84513
                                                                    =
                                                                    let uu____84514
                                                                    =
                                                                    let uu____84520
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84520,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84514
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84513
                                                                     in
                                                                    let uu____84523
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84523
                                                                    then
                                                                    let x =
                                                                    let uu____84527
                                                                    =
                                                                    let uu____84533
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84533,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84527
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84538
                                                                    =
                                                                    let uu____84546
                                                                    =
                                                                    let uu____84547
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84548
                                                                    =
                                                                    let uu____84559
                                                                    =
                                                                    let uu____84564
                                                                    =
                                                                    let uu____84567
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84567]
                                                                     in
                                                                    [uu____84564]
                                                                     in
                                                                    let uu____84572
                                                                    =
                                                                    let uu____84573
                                                                    =
                                                                    let uu____84578
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84580
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84578,
                                                                    uu____84580)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84573
                                                                     in
                                                                    (uu____84559,
                                                                    [x],
                                                                    uu____84572)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84547
                                                                    uu____84548
                                                                     in
                                                                    let uu____84601
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84546,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84601)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84538
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84612
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
                                                                    (let uu____84635
                                                                    =
                                                                    let uu____84636
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84636
                                                                    dapp1  in
                                                                    [uu____84635])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84612
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84643
                                                                    =
                                                                    let uu____84651
                                                                    =
                                                                    let uu____84652
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84653
                                                                    =
                                                                    let uu____84664
                                                                    =
                                                                    let uu____84665
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84665
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84667
                                                                    =
                                                                    let uu____84668
                                                                    =
                                                                    let uu____84673
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84673)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84668
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84664,
                                                                    uu____84667)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84652
                                                                    uu____84653
                                                                     in
                                                                    (uu____84651,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84643)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84690 ->
                                                         ((let uu____84692 =
                                                             let uu____84698
                                                               =
                                                               let uu____84700
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84702
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84700
                                                                 uu____84702
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84698)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84692);
                                                          ([], [])))
                                                 in
                                              let uu____84710 =
                                                encode_elim ()  in
                                              (match uu____84710 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84736 =
                                                       let uu____84739 =
                                                         let uu____84742 =
                                                           let uu____84745 =
                                                             let uu____84748
                                                               =
                                                               let uu____84751
                                                                 =
                                                                 let uu____84754
                                                                   =
                                                                   let uu____84755
                                                                    =
                                                                    let uu____84767
                                                                    =
                                                                    let uu____84768
                                                                    =
                                                                    let uu____84770
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84770
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84768
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84767)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84755
                                                                    in
                                                                 [uu____84754]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84751
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84748
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84781 =
                                                             let uu____84784
                                                               =
                                                               let uu____84787
                                                                 =
                                                                 let uu____84790
                                                                   =
                                                                   let uu____84793
                                                                    =
                                                                    let uu____84796
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84801
                                                                    =
                                                                    let uu____84804
                                                                    =
                                                                    let uu____84805
                                                                    =
                                                                    let uu____84813
                                                                    =
                                                                    let uu____84814
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84815
                                                                    =
                                                                    let uu____84826
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84826)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84814
                                                                    uu____84815
                                                                     in
                                                                    (uu____84813,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84805
                                                                     in
                                                                    let uu____84839
                                                                    =
                                                                    let uu____84842
                                                                    =
                                                                    let uu____84843
                                                                    =
                                                                    let uu____84851
                                                                    =
                                                                    let uu____84852
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84853
                                                                    =
                                                                    let uu____84864
                                                                    =
                                                                    let uu____84865
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84865
                                                                    vars'  in
                                                                    let uu____84867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84864,
                                                                    uu____84867)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84852
                                                                    uu____84853
                                                                     in
                                                                    (uu____84851,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84843
                                                                     in
                                                                    [uu____84842]
                                                                     in
                                                                    uu____84804
                                                                    ::
                                                                    uu____84839
                                                                     in
                                                                    uu____84796
                                                                    ::
                                                                    uu____84801
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84793
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84790
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84787
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84784
                                                              in
                                                           FStar_List.append
                                                             uu____84745
                                                             uu____84781
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84742
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84739
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84736
                                                      in
                                                   let uu____84884 =
                                                     let uu____84885 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84885 g
                                                      in
                                                   (uu____84884, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84919  ->
              fun se  ->
                match uu____84919 with
                | (g,env1) ->
                    let uu____84939 = encode_sigelt env1 se  in
                    (match uu____84939 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____85007 =
        match uu____85007 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____85044 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____85052 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____85052
                   then
                     let uu____85057 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____85059 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____85061 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____85057 uu____85059 uu____85061
                   else ());
                  (let uu____85066 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____85066 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____85084 =
                         let uu____85092 =
                           let uu____85094 =
                             let uu____85096 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85096
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85094  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85092
                          in
                       (match uu____85084 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85116 = FStar_Options.log_queries ()
                                 in
                              if uu____85116
                              then
                                let uu____85119 =
                                  let uu____85121 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85123 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85125 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85121 uu____85123 uu____85125
                                   in
                                FStar_Pervasives_Native.Some uu____85119
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85141 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85151 =
                                let uu____85154 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85154  in
                              FStar_List.append uu____85141 uu____85151  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85166,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85186 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85186 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85207 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85207 with | (uu____85234,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85287  ->
              match uu____85287 with
              | (l,uu____85296,uu____85297) ->
                  let uu____85300 =
                    let uu____85312 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85312, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85300))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85345  ->
              match uu____85345 with
              | (l,uu____85356,uu____85357) ->
                  let uu____85360 =
                    let uu____85361 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85364  -> FStar_SMTEncoding_Term.Echo _85364)
                      uu____85361
                     in
                  let uu____85365 =
                    let uu____85368 =
                      let uu____85369 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85369  in
                    [uu____85368]  in
                  uu____85360 :: uu____85365))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85387 =
      let uu____85390 =
        let uu____85391 = FStar_Util.psmap_empty ()  in
        let uu____85406 =
          let uu____85415 = FStar_Util.psmap_empty ()  in (uu____85415, [])
           in
        let uu____85422 =
          let uu____85424 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85424 FStar_Ident.string_of_lid  in
        let uu____85426 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85391;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85406;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85422;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85426
        }  in
      [uu____85390]  in
    FStar_ST.op_Colon_Equals last_env uu____85387
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85470 = FStar_ST.op_Bang last_env  in
      match uu____85470 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85498 ->
          let uu___2182_85501 = e  in
          let uu____85502 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2182_85501.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2182_85501.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2182_85501.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2182_85501.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2182_85501.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2182_85501.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2182_85501.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85502;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2182_85501.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2182_85501.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85510 = FStar_ST.op_Bang last_env  in
    match uu____85510 with
    | [] -> failwith "Empty env stack"
    | uu____85537::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85569  ->
    let uu____85570 = FStar_ST.op_Bang last_env  in
    match uu____85570 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85630  ->
    let uu____85631 = FStar_ST.op_Bang last_env  in
    match uu____85631 with
    | [] -> failwith "Popping an empty stack"
    | uu____85658::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85695  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85748  ->
         let uu____85749 = snapshot_env ()  in
         match uu____85749 with
         | (env_depth,()) ->
             let uu____85771 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85771 with
              | (varops_depth,()) ->
                  let uu____85793 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85793 with
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
        (fun uu____85851  ->
           let uu____85852 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85852 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85947 = snapshot msg  in () 
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
        | (uu____85993::uu____85994,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2243_86002 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2243_86002.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2243_86002.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2243_86002.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____86003 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2249_86030 = elt  in
        let uu____86031 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2249_86030.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2249_86030.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____86031;
          FStar_SMTEncoding_Term.a_names =
            (uu___2249_86030.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____86051 =
        let uu____86054 =
          let uu____86055 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____86055  in
        let uu____86056 = open_fact_db_tags env  in uu____86054 ::
          uu____86056
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____86051
  
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
      let uu____86083 = encode_sigelt env se  in
      match uu____86083 with
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
                (let uu____86129 =
                   let uu____86132 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86132
                    in
                 match uu____86129 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86147 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86147
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86177 = FStar_Options.log_queries ()  in
        if uu____86177
        then
          let uu____86182 =
            let uu____86183 =
              let uu____86185 =
                let uu____86187 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86187 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86185  in
            FStar_SMTEncoding_Term.Caption uu____86183  in
          uu____86182 :: decls
        else decls  in
      (let uu____86206 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86206
       then
         let uu____86209 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86209
       else ());
      (let env =
         let uu____86215 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86215 tcenv  in
       let uu____86216 = encode_top_level_facts env se  in
       match uu____86216 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86230 =
               let uu____86233 =
                 let uu____86236 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86236
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86233  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86230)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86269 = FStar_Options.log_queries ()  in
          if uu____86269
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2287_86289 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2287_86289.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2287_86289.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2287_86289.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2287_86289.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2287_86289.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2287_86289.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2287_86289.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2287_86289.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2287_86289.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2287_86289.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86294 =
             let uu____86297 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86297
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86294  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86317 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86317
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
          (let uu____86341 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86341
           then
             let uu____86344 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86344
           else ());
          (let env =
             let uu____86352 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86352
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86391  ->
                     fun se  ->
                       match uu____86391 with
                       | (g,env2) ->
                           let uu____86411 = encode_top_level_facts env2 se
                              in
                           (match uu____86411 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86434 =
             encode_signature
               (let uu___2310_86443 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2310_86443.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2310_86443.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2310_86443.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2310_86443.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2310_86443.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2310_86443.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2310_86443.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2310_86443.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2310_86443.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2310_86443.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86434 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86459 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86459
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86465 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86465))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86493  ->
        match uu____86493 with
        | (decls,fvbs) ->
            ((let uu____86507 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86507
              then ()
              else
                (let uu____86512 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86512
                 then
                   let uu____86515 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86515
                 else ()));
             (let env =
                let uu____86523 = get_env name tcenv  in
                FStar_All.pipe_right uu____86523
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86525 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86525
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86539 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86539
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
        (let uu____86601 =
           let uu____86603 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86603.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86601);
        (let env =
           let uu____86605 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86605 tcenv  in
         let uu____86606 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86645 = aux rest  in
                 (match uu____86645 with
                  | (out,rest1) ->
                      let t =
                        let uu____86673 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86673 with
                        | FStar_Pervasives_Native.Some uu____86676 ->
                            let uu____86677 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86677
                              x.FStar_Syntax_Syntax.sort
                        | uu____86678 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86682 =
                        let uu____86685 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2351_86688 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2351_86688.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2351_86688.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86685 :: out  in
                      (uu____86682, rest1))
             | uu____86693 -> ([], bindings)  in
           let uu____86700 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86700 with
           | (closing,bindings) ->
               let uu____86727 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86727, bindings)
            in
         match uu____86606 with
         | (q1,bindings) ->
             let uu____86758 = encode_env_bindings env bindings  in
             (match uu____86758 with
              | (env_decls,env1) ->
                  ((let uu____86780 =
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
                    if uu____86780
                    then
                      let uu____86787 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86787
                    else ());
                   (let uu____86792 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86792 with
                    | (phi,qdecls) ->
                        let uu____86813 =
                          let uu____86818 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86818 phi
                           in
                        (match uu____86813 with
                         | (labels,phi1) ->
                             let uu____86835 = encode_labels labels  in
                             (match uu____86835 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86871 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86871
                                    then
                                      let uu____86876 =
                                        let uu____86877 =
                                          let uu____86879 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86879
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86877
                                         in
                                      [uu____86876]
                                    else []  in
                                  let query_prelude =
                                    let uu____86887 =
                                      let uu____86888 =
                                        let uu____86889 =
                                          let uu____86892 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86899 =
                                            let uu____86902 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86902
                                             in
                                          FStar_List.append uu____86892
                                            uu____86899
                                           in
                                        FStar_List.append env_decls
                                          uu____86889
                                         in
                                      FStar_All.pipe_right uu____86888
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86887
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86912 =
                                      let uu____86920 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86921 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86920,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86921)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86912
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
  