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
  let uu____67913 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____67913 with
  | (asym,a) ->
      let uu____67924 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____67924 with
       | (xsym,x) ->
           let uu____67935 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____67935 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____68013 =
                      let uu____68025 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____68025, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____68013  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68045 =
                      let uu____68053 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68053)  in
                    FStar_SMTEncoding_Util.mkApp uu____68045  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68072 =
                    let uu____68075 =
                      let uu____68078 =
                        let uu____68081 =
                          let uu____68082 =
                            let uu____68090 =
                              let uu____68091 =
                                let uu____68102 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68102)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68091
                               in
                            (uu____68090, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68082  in
                        let uu____68114 =
                          let uu____68117 =
                            let uu____68118 =
                              let uu____68126 =
                                let uu____68127 =
                                  let uu____68138 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68138)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68127
                                 in
                              (uu____68126,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68118  in
                          [uu____68117]  in
                        uu____68081 :: uu____68114  in
                      xtok_decl :: uu____68078  in
                    xname_decl :: uu____68075  in
                  (xtok1, (FStar_List.length vars), uu____68072)  in
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
                  let uu____68308 =
                    let uu____68329 =
                      let uu____68348 =
                        let uu____68349 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____68349
                         in
                      quant axy uu____68348  in
                    (FStar_Parser_Const.op_Eq, uu____68329)  in
                  let uu____68366 =
                    let uu____68389 =
                      let uu____68410 =
                        let uu____68429 =
                          let uu____68430 =
                            let uu____68431 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____68431  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____68430
                           in
                        quant axy uu____68429  in
                      (FStar_Parser_Const.op_notEq, uu____68410)  in
                    let uu____68448 =
                      let uu____68471 =
                        let uu____68492 =
                          let uu____68511 =
                            let uu____68512 =
                              let uu____68513 =
                                let uu____68518 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____68519 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____68518, uu____68519)  in
                              FStar_SMTEncoding_Util.mkAnd uu____68513  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____68512
                             in
                          quant xy uu____68511  in
                        (FStar_Parser_Const.op_And, uu____68492)  in
                      let uu____68536 =
                        let uu____68559 =
                          let uu____68580 =
                            let uu____68599 =
                              let uu____68600 =
                                let uu____68601 =
                                  let uu____68606 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____68607 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____68606, uu____68607)  in
                                FStar_SMTEncoding_Util.mkOr uu____68601  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____68600
                               in
                            quant xy uu____68599  in
                          (FStar_Parser_Const.op_Or, uu____68580)  in
                        let uu____68624 =
                          let uu____68647 =
                            let uu____68668 =
                              let uu____68687 =
                                let uu____68688 =
                                  let uu____68689 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____68689
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____68688
                                 in
                              quant qx uu____68687  in
                            (FStar_Parser_Const.op_Negation, uu____68668)  in
                          let uu____68706 =
                            let uu____68729 =
                              let uu____68750 =
                                let uu____68769 =
                                  let uu____68770 =
                                    let uu____68771 =
                                      let uu____68776 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____68777 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____68776, uu____68777)  in
                                    FStar_SMTEncoding_Util.mkLT uu____68771
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____68770
                                   in
                                quant xy uu____68769  in
                              (FStar_Parser_Const.op_LT, uu____68750)  in
                            let uu____68794 =
                              let uu____68817 =
                                let uu____68838 =
                                  let uu____68857 =
                                    let uu____68858 =
                                      let uu____68859 =
                                        let uu____68864 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____68865 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____68864, uu____68865)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____68859
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____68858
                                     in
                                  quant xy uu____68857  in
                                (FStar_Parser_Const.op_LTE, uu____68838)  in
                              let uu____68882 =
                                let uu____68905 =
                                  let uu____68926 =
                                    let uu____68945 =
                                      let uu____68946 =
                                        let uu____68947 =
                                          let uu____68952 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____68953 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____68952, uu____68953)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____68947
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____68946
                                       in
                                    quant xy uu____68945  in
                                  (FStar_Parser_Const.op_GT, uu____68926)  in
                                let uu____68970 =
                                  let uu____68993 =
                                    let uu____69014 =
                                      let uu____69033 =
                                        let uu____69034 =
                                          let uu____69035 =
                                            let uu____69040 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69041 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69040, uu____69041)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69035
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69034
                                         in
                                      quant xy uu____69033  in
                                    (FStar_Parser_Const.op_GTE, uu____69014)
                                     in
                                  let uu____69058 =
                                    let uu____69081 =
                                      let uu____69102 =
                                        let uu____69121 =
                                          let uu____69122 =
                                            let uu____69123 =
                                              let uu____69128 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69129 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69128, uu____69129)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69123
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69122
                                           in
                                        quant xy uu____69121  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69102)
                                       in
                                    let uu____69146 =
                                      let uu____69169 =
                                        let uu____69190 =
                                          let uu____69209 =
                                            let uu____69210 =
                                              let uu____69211 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____69211
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____69210
                                             in
                                          quant qx uu____69209  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69190)
                                         in
                                      let uu____69228 =
                                        let uu____69251 =
                                          let uu____69272 =
                                            let uu____69291 =
                                              let uu____69292 =
                                                let uu____69293 =
                                                  let uu____69298 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____69299 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____69298, uu____69299)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____69293
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____69292
                                               in
                                            quant xy uu____69291  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____69272)
                                           in
                                        let uu____69316 =
                                          let uu____69339 =
                                            let uu____69360 =
                                              let uu____69379 =
                                                let uu____69380 =
                                                  let uu____69381 =
                                                    let uu____69386 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____69387 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____69386,
                                                      uu____69387)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____69381
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____69380
                                                 in
                                              quant xy uu____69379  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____69360)
                                             in
                                          let uu____69404 =
                                            let uu____69427 =
                                              let uu____69448 =
                                                let uu____69467 =
                                                  let uu____69468 =
                                                    let uu____69469 =
                                                      let uu____69474 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____69475 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____69474,
                                                        uu____69475)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____69469
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____69468
                                                   in
                                                quant xy uu____69467  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____69448)
                                               in
                                            let uu____69492 =
                                              let uu____69515 =
                                                let uu____69536 =
                                                  let uu____69555 =
                                                    let uu____69556 =
                                                      let uu____69557 =
                                                        let uu____69562 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____69563 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____69562,
                                                          uu____69563)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____69557
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____69556
                                                     in
                                                  quant xy uu____69555  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____69536)
                                                 in
                                              let uu____69580 =
                                                let uu____69603 =
                                                  let uu____69624 =
                                                    let uu____69643 =
                                                      let uu____69644 =
                                                        let uu____69645 =
                                                          let uu____69650 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____69651 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____69650,
                                                            uu____69651)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____69645
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____69644
                                                       in
                                                    quant xy uu____69643  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____69624)
                                                   in
                                                let uu____69668 =
                                                  let uu____69691 =
                                                    let uu____69712 =
                                                      let uu____69731 =
                                                        let uu____69732 =
                                                          let uu____69733 =
                                                            let uu____69738 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____69739 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____69738,
                                                              uu____69739)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____69733
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____69732
                                                         in
                                                      quant xy uu____69731
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____69712)
                                                     in
                                                  let uu____69756 =
                                                    let uu____69779 =
                                                      let uu____69800 =
                                                        let uu____69819 =
                                                          let uu____69820 =
                                                            let uu____69821 =
                                                              let uu____69826
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____69827
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____69826,
                                                                uu____69827)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____69821
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____69820
                                                           in
                                                        quant xy uu____69819
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____69800)
                                                       in
                                                    let uu____69844 =
                                                      let uu____69867 =
                                                        let uu____69888 =
                                                          let uu____69907 =
                                                            let uu____69908 =
                                                              let uu____69909
                                                                =
                                                                let uu____69914
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____69915
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____69914,
                                                                  uu____69915)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____69909
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____69908
                                                             in
                                                          quant xy
                                                            uu____69907
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____69888)
                                                         in
                                                      let uu____69932 =
                                                        let uu____69955 =
                                                          let uu____69976 =
                                                            let uu____69995 =
                                                              let uu____69996
                                                                =
                                                                let uu____69997
                                                                  =
                                                                  let uu____70002
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____70003
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____70002,
                                                                    uu____70003)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____69997
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____69996
                                                               in
                                                            quant xy
                                                              uu____69995
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____69976)
                                                           in
                                                        let uu____70020 =
                                                          let uu____70043 =
                                                            let uu____70064 =
                                                              let uu____70083
                                                                =
                                                                let uu____70084
                                                                  =
                                                                  let uu____70085
                                                                    =
                                                                    let uu____70090
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70091
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70090,
                                                                    uu____70091)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70085
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70084
                                                                 in
                                                              quant xy
                                                                uu____70083
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70064)
                                                             in
                                                          let uu____70108 =
                                                            let uu____70131 =
                                                              let uu____70152
                                                                =
                                                                let uu____70171
                                                                  =
                                                                  let uu____70172
                                                                    =
                                                                    let uu____70173
                                                                    =
                                                                    let uu____70178
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70179
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70178,
                                                                    uu____70179)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70173
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70172
                                                                   in
                                                                quant xy
                                                                  uu____70171
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70152)
                                                               in
                                                            let uu____70196 =
                                                              let uu____70219
                                                                =
                                                                let uu____70240
                                                                  =
                                                                  let uu____70259
                                                                    =
                                                                    let uu____70260
                                                                    =
                                                                    let uu____70261
                                                                    =
                                                                    let uu____70266
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70267
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70266,
                                                                    uu____70267)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____70261
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70260
                                                                     in
                                                                  quant xy
                                                                    uu____70259
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____70240)
                                                                 in
                                                              let uu____70284
                                                                =
                                                                let uu____70307
                                                                  =
                                                                  let uu____70328
                                                                    =
                                                                    let uu____70347
                                                                    =
                                                                    let uu____70348
                                                                    =
                                                                    let uu____70349
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____70349
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70348
                                                                     in
                                                                    quant qx
                                                                    uu____70347
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____70328)
                                                                   in
                                                                [uu____70307]
                                                                 in
                                                              uu____70219 ::
                                                                uu____70284
                                                               in
                                                            uu____70131 ::
                                                              uu____70196
                                                             in
                                                          uu____70043 ::
                                                            uu____70108
                                                           in
                                                        uu____69955 ::
                                                          uu____70020
                                                         in
                                                      uu____69867 ::
                                                        uu____69932
                                                       in
                                                    uu____69779 ::
                                                      uu____69844
                                                     in
                                                  uu____69691 :: uu____69756
                                                   in
                                                uu____69603 :: uu____69668
                                                 in
                                              uu____69515 :: uu____69580  in
                                            uu____69427 :: uu____69492  in
                                          uu____69339 :: uu____69404  in
                                        uu____69251 :: uu____69316  in
                                      uu____69169 :: uu____69228  in
                                    uu____69081 :: uu____69146  in
                                  uu____68993 :: uu____69058  in
                                uu____68905 :: uu____68970  in
                              uu____68817 :: uu____68882  in
                            uu____68729 :: uu____68794  in
                          uu____68647 :: uu____68706  in
                        uu____68559 :: uu____68624  in
                      uu____68471 :: uu____68536  in
                    uu____68389 :: uu____68448  in
                  uu____68308 :: uu____68366  in
                let mk1 l v1 =
                  let uu____70888 =
                    let uu____70900 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____70990  ->
                              match uu____70990 with
                              | (l',uu____71011) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____70900
                      (FStar_Option.map
                         (fun uu____71110  ->
                            match uu____71110 with
                            | (uu____71138,b) ->
                                let uu____71172 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71172 v1))
                     in
                  FStar_All.pipe_right uu____70888 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____71255  ->
                          match uu____71255 with
                          | (l',uu____71276) -> FStar_Ident.lid_equals l l'))
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
          let uu____71350 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____71350 with
          | (xxsym,xx) ->
              let uu____71361 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____71361 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____71377 =
                     let uu____71385 =
                       let uu____71386 =
                         let uu____71397 =
                           let uu____71398 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____71408 =
                             let uu____71419 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____71419 :: vars  in
                           uu____71398 :: uu____71408  in
                         let uu____71445 =
                           let uu____71446 =
                             let uu____71451 =
                               let uu____71452 =
                                 let uu____71457 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____71457)  in
                               FStar_SMTEncoding_Util.mkEq uu____71452  in
                             (xx_has_type, uu____71451)  in
                           FStar_SMTEncoding_Util.mkImp uu____71446  in
                         ([[xx_has_type]], uu____71397, uu____71445)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____71386  in
                     let uu____71470 =
                       let uu____71472 =
                         let uu____71474 =
                           let uu____71476 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____71476  in
                         Prims.op_Hat module_name uu____71474  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____71472
                        in
                     (uu____71385,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____71470)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____71377)
  
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
    let uu____71532 =
      let uu____71534 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____71534  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____71532  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____71556 =
      let uu____71557 =
        let uu____71565 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____71565, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71557  in
    let uu____71570 =
      let uu____71573 =
        let uu____71574 =
          let uu____71582 =
            let uu____71583 =
              let uu____71594 =
                let uu____71595 =
                  let uu____71600 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____71600)  in
                FStar_SMTEncoding_Util.mkImp uu____71595  in
              ([[typing_pred]], [xx], uu____71594)  in
            let uu____71625 =
              let uu____71640 = FStar_TypeChecker_Env.get_range env  in
              let uu____71641 = mkForall_fuel1 env  in
              uu____71641 uu____71640  in
            uu____71625 uu____71583  in
          (uu____71582, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71574  in
      [uu____71573]  in
    uu____71556 :: uu____71570  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____71688 =
      let uu____71689 =
        let uu____71697 =
          let uu____71698 = FStar_TypeChecker_Env.get_range env  in
          let uu____71699 =
            let uu____71710 =
              let uu____71715 =
                let uu____71718 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____71718]  in
              [uu____71715]  in
            let uu____71723 =
              let uu____71724 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71724 tt  in
            (uu____71710, [bb], uu____71723)  in
          FStar_SMTEncoding_Term.mkForall uu____71698 uu____71699  in
        (uu____71697, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71689  in
    let uu____71749 =
      let uu____71752 =
        let uu____71753 =
          let uu____71761 =
            let uu____71762 =
              let uu____71773 =
                let uu____71774 =
                  let uu____71779 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____71779)  in
                FStar_SMTEncoding_Util.mkImp uu____71774  in
              ([[typing_pred]], [xx], uu____71773)  in
            let uu____71806 =
              let uu____71821 = FStar_TypeChecker_Env.get_range env  in
              let uu____71822 = mkForall_fuel1 env  in
              uu____71822 uu____71821  in
            uu____71806 uu____71762  in
          (uu____71761, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71753  in
      [uu____71752]  in
    uu____71688 :: uu____71749  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____71865 =
        let uu____71866 =
          let uu____71872 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____71872, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____71866  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71865  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____71886 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____71886  in
    let uu____71891 =
      let uu____71892 =
        let uu____71900 =
          let uu____71901 = FStar_TypeChecker_Env.get_range env  in
          let uu____71902 =
            let uu____71913 =
              let uu____71918 =
                let uu____71921 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____71921]  in
              [uu____71918]  in
            let uu____71926 =
              let uu____71927 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____71927 tt  in
            (uu____71913, [bb], uu____71926)  in
          FStar_SMTEncoding_Term.mkForall uu____71901 uu____71902  in
        (uu____71900, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____71892  in
    let uu____71952 =
      let uu____71955 =
        let uu____71956 =
          let uu____71964 =
            let uu____71965 =
              let uu____71976 =
                let uu____71977 =
                  let uu____71982 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____71982)  in
                FStar_SMTEncoding_Util.mkImp uu____71977  in
              ([[typing_pred]], [xx], uu____71976)  in
            let uu____72009 =
              let uu____72024 = FStar_TypeChecker_Env.get_range env  in
              let uu____72025 = mkForall_fuel1 env  in
              uu____72025 uu____72024  in
            uu____72009 uu____71965  in
          (uu____71964, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____71956  in
      let uu____72047 =
        let uu____72050 =
          let uu____72051 =
            let uu____72059 =
              let uu____72060 =
                let uu____72071 =
                  let uu____72072 =
                    let uu____72077 =
                      let uu____72078 =
                        let uu____72081 =
                          let uu____72084 =
                            let uu____72087 =
                              let uu____72088 =
                                let uu____72093 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72094 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72093, uu____72094)  in
                              FStar_SMTEncoding_Util.mkGT uu____72088  in
                            let uu____72096 =
                              let uu____72099 =
                                let uu____72100 =
                                  let uu____72105 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72106 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72105, uu____72106)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72100  in
                              let uu____72108 =
                                let uu____72111 =
                                  let uu____72112 =
                                    let uu____72117 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72118 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72117, uu____72118)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72112  in
                                [uu____72111]  in
                              uu____72099 :: uu____72108  in
                            uu____72087 :: uu____72096  in
                          typing_pred_y :: uu____72084  in
                        typing_pred :: uu____72081  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72078  in
                    (uu____72077, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72072  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72071)
                 in
              let uu____72151 =
                let uu____72166 = FStar_TypeChecker_Env.get_range env  in
                let uu____72167 = mkForall_fuel1 env  in
                uu____72167 uu____72166  in
              uu____72151 uu____72060  in
            (uu____72059,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72051  in
        [uu____72050]  in
      uu____71955 :: uu____72047  in
    uu____71891 :: uu____71952  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____72210 =
        let uu____72211 =
          let uu____72217 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72217, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72211  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72210  in
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
      let uu____72233 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72233  in
    let uu____72238 =
      let uu____72239 =
        let uu____72247 =
          let uu____72248 = FStar_TypeChecker_Env.get_range env  in
          let uu____72249 =
            let uu____72260 =
              let uu____72265 =
                let uu____72268 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____72268]  in
              [uu____72265]  in
            let uu____72273 =
              let uu____72274 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72274 tt  in
            (uu____72260, [bb], uu____72273)  in
          FStar_SMTEncoding_Term.mkForall uu____72248 uu____72249  in
        (uu____72247, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72239  in
    let uu____72299 =
      let uu____72302 =
        let uu____72303 =
          let uu____72311 =
            let uu____72312 =
              let uu____72323 =
                let uu____72324 =
                  let uu____72329 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____72329)  in
                FStar_SMTEncoding_Util.mkImp uu____72324  in
              ([[typing_pred]], [xx], uu____72323)  in
            let uu____72356 =
              let uu____72371 = FStar_TypeChecker_Env.get_range env  in
              let uu____72372 = mkForall_fuel1 env  in
              uu____72372 uu____72371  in
            uu____72356 uu____72312  in
          (uu____72311, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72303  in
      let uu____72394 =
        let uu____72397 =
          let uu____72398 =
            let uu____72406 =
              let uu____72407 =
                let uu____72418 =
                  let uu____72419 =
                    let uu____72424 =
                      let uu____72425 =
                        let uu____72428 =
                          let uu____72431 =
                            let uu____72434 =
                              let uu____72435 =
                                let uu____72440 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____72441 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____72440, uu____72441)  in
                              FStar_SMTEncoding_Util.mkGT uu____72435  in
                            let uu____72443 =
                              let uu____72446 =
                                let uu____72447 =
                                  let uu____72452 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____72453 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____72452, uu____72453)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72447  in
                              let uu____72455 =
                                let uu____72458 =
                                  let uu____72459 =
                                    let uu____72464 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____72465 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____72464, uu____72465)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72459  in
                                [uu____72458]  in
                              uu____72446 :: uu____72455  in
                            uu____72434 :: uu____72443  in
                          typing_pred_y :: uu____72431  in
                        typing_pred :: uu____72428  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72425  in
                    (uu____72424, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72419  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72418)
                 in
              let uu____72498 =
                let uu____72513 = FStar_TypeChecker_Env.get_range env  in
                let uu____72514 = mkForall_fuel1 env  in
                uu____72514 uu____72513  in
              uu____72498 uu____72407  in
            (uu____72406,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72398  in
        [uu____72397]  in
      uu____72302 :: uu____72394  in
    uu____72238 :: uu____72299  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72561 =
      let uu____72562 =
        let uu____72570 =
          let uu____72571 = FStar_TypeChecker_Env.get_range env  in
          let uu____72572 =
            let uu____72583 =
              let uu____72588 =
                let uu____72591 = FStar_SMTEncoding_Term.boxString b  in
                [uu____72591]  in
              [uu____72588]  in
            let uu____72596 =
              let uu____72597 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72597 tt  in
            (uu____72583, [bb], uu____72596)  in
          FStar_SMTEncoding_Term.mkForall uu____72571 uu____72572  in
        (uu____72570, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72562  in
    let uu____72622 =
      let uu____72625 =
        let uu____72626 =
          let uu____72634 =
            let uu____72635 =
              let uu____72646 =
                let uu____72647 =
                  let uu____72652 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____72652)  in
                FStar_SMTEncoding_Util.mkImp uu____72647  in
              ([[typing_pred]], [xx], uu____72646)  in
            let uu____72679 =
              let uu____72694 = FStar_TypeChecker_Env.get_range env  in
              let uu____72695 = mkForall_fuel1 env  in
              uu____72695 uu____72694  in
            uu____72679 uu____72635  in
          (uu____72634, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72626  in
      [uu____72625]  in
    uu____72561 :: uu____72622  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____72742 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____72742]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____72772 =
      let uu____72773 =
        let uu____72781 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____72781, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72773  in
    [uu____72772]  in
  let mk_and_interp env conj uu____72804 =
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
    let uu____72833 =
      let uu____72834 =
        let uu____72842 =
          let uu____72843 = FStar_TypeChecker_Env.get_range env  in
          let uu____72844 =
            let uu____72855 =
              let uu____72856 =
                let uu____72861 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____72861, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72856  in
            ([[l_and_a_b]], [aa; bb], uu____72855)  in
          FStar_SMTEncoding_Term.mkForall uu____72843 uu____72844  in
        (uu____72842, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72834  in
    [uu____72833]  in
  let mk_or_interp env disj uu____72916 =
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
    let uu____72945 =
      let uu____72946 =
        let uu____72954 =
          let uu____72955 = FStar_TypeChecker_Env.get_range env  in
          let uu____72956 =
            let uu____72967 =
              let uu____72968 =
                let uu____72973 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____72973, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____72968  in
            ([[l_or_a_b]], [aa; bb], uu____72967)  in
          FStar_SMTEncoding_Term.mkForall uu____72955 uu____72956  in
        (uu____72954, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72946  in
    [uu____72945]  in
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
    let uu____73051 =
      let uu____73052 =
        let uu____73060 =
          let uu____73061 = FStar_TypeChecker_Env.get_range env  in
          let uu____73062 =
            let uu____73073 =
              let uu____73074 =
                let uu____73079 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73079, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73074  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73073)  in
          FStar_SMTEncoding_Term.mkForall uu____73061 uu____73062  in
        (uu____73060, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73052  in
    [uu____73051]  in
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
    let uu____73169 =
      let uu____73170 =
        let uu____73178 =
          let uu____73179 = FStar_TypeChecker_Env.get_range env  in
          let uu____73180 =
            let uu____73191 =
              let uu____73192 =
                let uu____73197 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73197, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73192  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73191)  in
          FStar_SMTEncoding_Term.mkForall uu____73179 uu____73180  in
        (uu____73178, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73170  in
    [uu____73169]  in
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
    let uu____73297 =
      let uu____73298 =
        let uu____73306 =
          let uu____73307 = FStar_TypeChecker_Env.get_range env  in
          let uu____73308 =
            let uu____73319 =
              let uu____73320 =
                let uu____73325 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____73325, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73320  in
            ([[l_imp_a_b]], [aa; bb], uu____73319)  in
          FStar_SMTEncoding_Term.mkForall uu____73307 uu____73308  in
        (uu____73306, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73298  in
    [uu____73297]  in
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
    let uu____73409 =
      let uu____73410 =
        let uu____73418 =
          let uu____73419 = FStar_TypeChecker_Env.get_range env  in
          let uu____73420 =
            let uu____73431 =
              let uu____73432 =
                let uu____73437 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____73437, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73432  in
            ([[l_iff_a_b]], [aa; bb], uu____73431)  in
          FStar_SMTEncoding_Term.mkForall uu____73419 uu____73420  in
        (uu____73418, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73410  in
    [uu____73409]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____73508 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____73508  in
    let uu____73513 =
      let uu____73514 =
        let uu____73522 =
          let uu____73523 = FStar_TypeChecker_Env.get_range env  in
          let uu____73524 =
            let uu____73535 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____73535)  in
          FStar_SMTEncoding_Term.mkForall uu____73523 uu____73524  in
        (uu____73522, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73514  in
    [uu____73513]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____73588 =
      let uu____73589 =
        let uu____73597 =
          let uu____73598 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____73598 range_ty  in
        let uu____73599 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____73597, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____73599)
         in
      FStar_SMTEncoding_Util.mkAssume uu____73589  in
    [uu____73588]  in
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
        let uu____73645 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____73645 x1 t  in
      let uu____73647 = FStar_TypeChecker_Env.get_range env  in
      let uu____73648 =
        let uu____73659 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____73659)  in
      FStar_SMTEncoding_Term.mkForall uu____73647 uu____73648  in
    let uu____73684 =
      let uu____73685 =
        let uu____73693 =
          let uu____73694 = FStar_TypeChecker_Env.get_range env  in
          let uu____73695 =
            let uu____73706 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____73706)  in
          FStar_SMTEncoding_Term.mkForall uu____73694 uu____73695  in
        (uu____73693,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73685  in
    [uu____73684]  in
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
    let uu____73767 =
      let uu____73768 =
        let uu____73776 =
          let uu____73777 = FStar_TypeChecker_Env.get_range env  in
          let uu____73778 =
            let uu____73794 =
              let uu____73795 =
                let uu____73800 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____73801 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____73800, uu____73801)  in
              FStar_SMTEncoding_Util.mkAnd uu____73795  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____73794)
             in
          FStar_SMTEncoding_Term.mkForall' uu____73777 uu____73778  in
        (uu____73776,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73768  in
    [uu____73767]  in
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
          let uu____74359 =
            FStar_Util.find_opt
              (fun uu____74397  ->
                 match uu____74397 with
                 | (l,uu____74413) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____74359 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____74456,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____74517 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____74517 with
        | (form,decls) ->
            let uu____74526 =
              let uu____74529 =
                let uu____74532 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____74532]  in
              FStar_All.pipe_right uu____74529
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____74526
  
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
              let uu____74591 =
                ((let uu____74595 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____74595) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____74591
              then
                let arg_sorts =
                  let uu____74607 =
                    let uu____74608 = FStar_Syntax_Subst.compress t_norm  in
                    uu____74608.FStar_Syntax_Syntax.n  in
                  match uu____74607 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____74614) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____74652  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____74659 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____74661 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____74661 with
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
                    let uu____74693 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____74693, env1)
              else
                (let uu____74698 = prims.is lid  in
                 if uu____74698
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____74707 = prims.mk lid vname  in
                   match uu____74707 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____74731 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____74731, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____74740 =
                      let uu____74759 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____74759 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____74787 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____74787
                            then
                              let uu____74792 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_74795 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_74795.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_74795.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_74795.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_74795.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_74795.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_74795.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_74795.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_74795.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_74795.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_74795.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_74795.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_74795.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_74795.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_74795.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_74795.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_74795.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_74795.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_74795.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_74795.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_74795.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_74795.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_74795.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_74795.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_74795.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_74795.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_74795.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_74795.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_74795.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_74795.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_74795.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_74795.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_74795.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_74795.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_74795.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_74795.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_74795.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_74795.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_74795.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_74795.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_74795.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_74795.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_74795.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____74792
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____74818 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____74818)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____74740 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_74924  ->
                                  match uu___639_74924 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____74928 =
                                        FStar_Util.prefix vars  in
                                      (match uu____74928 with
                                       | (uu____74961,xxv) ->
                                           let xx =
                                             let uu____75000 =
                                               let uu____75001 =
                                                 let uu____75007 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75007,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75001
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75000
                                              in
                                           let uu____75010 =
                                             let uu____75011 =
                                               let uu____75019 =
                                                 let uu____75020 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75021 =
                                                   let uu____75032 =
                                                     let uu____75033 =
                                                       let uu____75038 =
                                                         let uu____75039 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75039
                                                          in
                                                       (vapp, uu____75038)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75033
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75032)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75020 uu____75021
                                                  in
                                               (uu____75019,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75011
                                              in
                                           [uu____75010])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75054 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75054 with
                                       | (uu____75087,xxv) ->
                                           let xx =
                                             let uu____75126 =
                                               let uu____75127 =
                                                 let uu____75133 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75133,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75127
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75126
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
                                           let uu____75144 =
                                             let uu____75145 =
                                               let uu____75153 =
                                                 let uu____75154 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75155 =
                                                   let uu____75166 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75166)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75154 uu____75155
                                                  in
                                               (uu____75153,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75145
                                              in
                                           [uu____75144])
                                  | uu____75179 -> []))
                           in
                        let uu____75180 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75180 with
                         | (vars,guards,env',decls1,uu____75205) ->
                             let uu____75218 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____75231 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____75231, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____75235 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____75235 with
                                    | (g,ds) ->
                                        let uu____75248 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____75248,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____75218 with
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
                                  let should_thunk uu____75271 =
                                    let is_type1 t =
                                      let uu____75279 =
                                        let uu____75280 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____75280.FStar_Syntax_Syntax.n  in
                                      match uu____75279 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____75284 -> true
                                      | uu____75286 -> false  in
                                    let is_squash1 t =
                                      let uu____75295 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____75295 with
                                      | (head1,uu____75314) ->
                                          let uu____75339 =
                                            let uu____75340 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____75340.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____75339 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____75345;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____75346;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____75348;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____75349;_};_},uu____75350)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____75358 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____75363 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____75363))
                                       &&
                                       (let uu____75369 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____75369))
                                      &&
                                      (let uu____75372 = is_type1 t_norm  in
                                       Prims.op_Negation uu____75372)
                                     in
                                  let uu____75374 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____75433 -> (false, vars)  in
                                  (match uu____75374 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____75483 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____75483 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____75515 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____75524 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____75524
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____75535 ->
                                                  let uu____75544 =
                                                    let uu____75552 =
                                                      get_vtok ()  in
                                                    (uu____75552, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____75544
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____75559 =
                                                let uu____75567 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____75567)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____75559
                                               in
                                            let uu____75581 =
                                              let vname_decl =
                                                let uu____75589 =
                                                  let uu____75601 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____75601,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____75589
                                                 in
                                              let uu____75612 =
                                                let env2 =
                                                  let uu___1026_75618 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_75618.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____75619 =
                                                  let uu____75621 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____75621
                                                   in
                                                if uu____75619
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____75612 with
                                              | (tok_typing,decls2) ->
                                                  let uu____75638 =
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
                                                        let uu____75664 =
                                                          let uu____75667 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75667
                                                           in
                                                        let uu____75674 =
                                                          let uu____75675 =
                                                            let uu____75678 =
                                                              let uu____75679
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____75679
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _75683  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _75683)
                                                              uu____75678
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____75675
                                                           in
                                                        (uu____75664,
                                                          uu____75674)
                                                    | uu____75686 when
                                                        thunked ->
                                                        let uu____75697 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____75697
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____75712
                                                                 =
                                                                 let uu____75720
                                                                   =
                                                                   let uu____75723
                                                                    =
                                                                    let uu____75726
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____75726]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____75723
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____75720)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____75712
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____75734
                                                               =
                                                               let uu____75742
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____75742,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____75734
                                                              in
                                                           let uu____75747 =
                                                             let uu____75750
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____75750
                                                              in
                                                           (uu____75747,
                                                             env1))
                                                    | uu____75759 ->
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
                                                          let uu____75783 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____75784 =
                                                            let uu____75795 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____75795)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____75783
                                                            uu____75784
                                                           in
                                                        let name_tok_corr =
                                                          let uu____75805 =
                                                            let uu____75813 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____75813,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____75805
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
                                                            let uu____75824 =
                                                              let uu____75825
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____75825]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____75824
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____75852 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75853 =
                                                              let uu____75864
                                                                =
                                                                let uu____75865
                                                                  =
                                                                  let uu____75870
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____75871
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____75870,
                                                                    uu____75871)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____75865
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____75864)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75852
                                                              uu____75853
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____75900 =
                                                          let uu____75903 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____75903
                                                           in
                                                        (uu____75900, env1)
                                                     in
                                                  (match uu____75638 with
                                                   | (tok_decl,env2) ->
                                                       let uu____75924 =
                                                         let uu____75927 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____75927
                                                           tok_decl
                                                          in
                                                       (uu____75924, env2))
                                               in
                                            (match uu____75581 with
                                             | (decls2,env2) ->
                                                 let uu____75946 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____75956 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____75956 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____75971 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____75971, decls)
                                                    in
                                                 (match uu____75946 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____75986 =
                                                          let uu____75994 =
                                                            let uu____75995 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____75996 =
                                                              let uu____76007
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____76007)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____75995
                                                              uu____75996
                                                             in
                                                          (uu____75994,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____75986
                                                         in
                                                      let freshness =
                                                        let uu____76023 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____76023
                                                        then
                                                          let uu____76031 =
                                                            let uu____76032 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76033 =
                                                              let uu____76046
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76053
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76046,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76053)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____76032
                                                              uu____76033
                                                             in
                                                          let uu____76059 =
                                                            let uu____76062 =
                                                              let uu____76063
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76063
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76062]  in
                                                          uu____76031 ::
                                                            uu____76059
                                                        else []  in
                                                      let g =
                                                        let uu____76069 =
                                                          let uu____76072 =
                                                            let uu____76075 =
                                                              let uu____76078
                                                                =
                                                                let uu____76081
                                                                  =
                                                                  let uu____76084
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76084
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76081
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76078
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76075
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76072
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76069
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
          let uu____76124 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76124 with
          | FStar_Pervasives_Native.None  ->
              let uu____76135 = encode_free_var false env x t t_norm []  in
              (match uu____76135 with
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
            let uu____76198 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76198 with
            | (decls,env1) ->
                let uu____76209 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____76209
                then
                  let uu____76216 =
                    let uu____76217 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____76217  in
                  (uu____76216, env1)
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
             (fun uu____76273  ->
                fun lb  ->
                  match uu____76273 with
                  | (decls,env1) ->
                      let uu____76293 =
                        let uu____76298 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____76298
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____76293 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____76327 = FStar_Syntax_Util.head_and_args t  in
    match uu____76327 with
    | (hd1,args) ->
        let uu____76371 =
          let uu____76372 = FStar_Syntax_Util.un_uinst hd1  in
          uu____76372.FStar_Syntax_Syntax.n  in
        (match uu____76371 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____76378,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____76402 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____76413 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_76421 = en  in
    let uu____76422 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_76421.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_76421.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_76421.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_76421.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_76421.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_76421.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_76421.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_76421.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_76421.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_76421.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____76422
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____76452  ->
      fun quals  ->
        match uu____76452 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____76557 = FStar_Util.first_N nbinders formals  in
              match uu____76557 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____76654  ->
                         fun uu____76655  ->
                           match (uu____76654, uu____76655) with
                           | ((formal,uu____76681),(binder,uu____76683)) ->
                               let uu____76704 =
                                 let uu____76711 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____76711)  in
                               FStar_Syntax_Syntax.NT uu____76704) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____76725 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____76766  ->
                              match uu____76766 with
                              | (x,i) ->
                                  let uu____76785 =
                                    let uu___1139_76786 = x  in
                                    let uu____76787 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_76786.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_76786.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76787
                                    }  in
                                  (uu____76785, i)))
                       in
                    FStar_All.pipe_right uu____76725
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____76811 =
                      let uu____76816 = FStar_Syntax_Subst.compress body  in
                      let uu____76817 =
                        let uu____76818 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____76818
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____76816
                        uu____76817
                       in
                    uu____76811 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_76867 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_76867.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_76867.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_76867.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_76867.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_76867.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_76867.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_76867.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_76867.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_76867.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_76867.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_76867.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_76867.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_76867.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_76867.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_76867.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_76867.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_76867.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_76867.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_76867.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_76867.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_76867.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_76867.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_76867.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_76867.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_76867.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_76867.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_76867.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_76867.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_76867.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_76867.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_76867.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_76867.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_76867.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_76867.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_76867.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_76867.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_76867.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_76867.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_76867.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_76867.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_76867.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_76867.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____76939  ->
                       fun uu____76940  ->
                         match (uu____76939, uu____76940) with
                         | ((x,uu____76966),(b,uu____76968)) ->
                             let uu____76989 =
                               let uu____76996 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____76996)  in
                             FStar_Syntax_Syntax.NT uu____76989) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____77021 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____77021
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77050 ->
                    let uu____77057 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77057
                | uu____77058 when Prims.op_Negation norm1 ->
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
                | uu____77061 ->
                    let uu____77062 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77062)
                 in
              let aux t1 e1 =
                let uu____77104 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77104 with
                | (binders,body,lopt) ->
                    let uu____77136 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77152 -> arrow_formals_comp_norm false t1  in
                    (match uu____77136 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77186 =
                           if nformals < nbinders
                           then
                             let uu____77220 =
                               FStar_Util.first_N nformals binders  in
                             match uu____77220 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____77300 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____77300)
                           else
                             if nformals > nbinders
                             then
                               (let uu____77330 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____77330 with
                                | (binders1,body1) ->
                                    let uu____77383 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____77383))
                             else
                               (let uu____77396 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____77396))
                            in
                         (match uu____77186 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____77456 = aux t e  in
              match uu____77456 with
              | (binders,body,comp) ->
                  let uu____77502 =
                    let uu____77513 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____77513
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____77528 = aux comp1 body1  in
                      match uu____77528 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____77502 with
                   | (binders1,body1,comp1) ->
                       let uu____77611 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____77611, comp1))
               in
            (try
               (fun uu___1216_77638  ->
                  match () with
                  | () ->
                      let uu____77645 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____77645
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____77661 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____77724  ->
                                   fun lb  ->
                                     match uu____77724 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____77779 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____77779
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____77785 =
                                             let uu____77794 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____77794
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____77785 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____77661 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____77935;
                                    FStar_Syntax_Syntax.lbeff = uu____77936;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____77938;
                                    FStar_Syntax_Syntax.lbpos = uu____77939;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____77963 =
                                     let uu____77970 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____77970 with
                                     | (tcenv',uu____77986,e_t) ->
                                         let uu____77992 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____78003 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____77992 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_78020 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_78020.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____77963 with
                                    | (env',e1,t_norm1) ->
                                        let uu____78030 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____78030 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78050 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78050
                                               then
                                                 let uu____78055 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78058 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78055 uu____78058
                                               else ());
                                              (let uu____78063 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78063 with
                                               | (vars,_guards,env'1,binder_decls,uu____78090)
                                                   ->
                                                   let uu____78103 =
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
                                                         let uu____78120 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78120
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78142 =
                                                          let uu____78143 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78144 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78143 fvb
                                                            uu____78144
                                                           in
                                                        (vars, uu____78142))
                                                      in
                                                   (match uu____78103 with
                                                    | (vars1,app) ->
                                                        let uu____78155 =
                                                          let is_logical =
                                                            let uu____78168 =
                                                              let uu____78169
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78169.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78168
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78175 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78179 =
                                                              let uu____78180
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78180
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78179
                                                              (fun lid  ->
                                                                 let uu____78189
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78189
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78190 =
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
                                                          if uu____78190
                                                          then
                                                            let uu____78206 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____78207 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____78206,
                                                              uu____78207)
                                                          else
                                                            (let uu____78218
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____78218))
                                                           in
                                                        (match uu____78155
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____78242
                                                                 =
                                                                 let uu____78250
                                                                   =
                                                                   let uu____78251
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____78252
                                                                    =
                                                                    let uu____78263
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____78263)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____78251
                                                                    uu____78252
                                                                    in
                                                                 let uu____78272
                                                                   =
                                                                   let uu____78273
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____78273
                                                                    in
                                                                 (uu____78250,
                                                                   uu____78272,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____78242
                                                                in
                                                             let uu____78279
                                                               =
                                                               let uu____78282
                                                                 =
                                                                 let uu____78285
                                                                   =
                                                                   let uu____78288
                                                                    =
                                                                    let uu____78291
                                                                    =
                                                                    let uu____78294
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____78294
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____78291
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____78288
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____78285
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____78282
                                                                in
                                                             (uu____78279,
                                                               env2)))))))
                               | uu____78303 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____78363 =
                                   let uu____78369 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____78369,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____78363  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____78375 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____78428  ->
                                         fun fvb  ->
                                           match uu____78428 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____78483 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78483
                                                  in
                                               let gtok =
                                                 let uu____78487 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____78487
                                                  in
                                               let env4 =
                                                 let uu____78490 =
                                                   let uu____78493 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _78499  ->
                                                        FStar_Pervasives_Native.Some
                                                          _78499) uu____78493
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____78490
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____78375 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____78619
                                     t_norm uu____78621 =
                                     match (uu____78619, uu____78621) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____78651;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____78652;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____78654;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____78655;_})
                                         ->
                                         let uu____78682 =
                                           let uu____78689 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____78689 with
                                           | (tcenv',uu____78705,e_t) ->
                                               let uu____78711 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____78722 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____78711 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_78739 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_78739.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____78682 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____78752 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____78752
                                                then
                                                  let uu____78757 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____78759 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____78761 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____78757 uu____78759
                                                    uu____78761
                                                else ());
                                               (let uu____78766 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____78766 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____78793 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____78793 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____78815 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____78815
                                                           then
                                                             let uu____78820
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____78822
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____78825
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____78827
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____78820
                                                               uu____78822
                                                               uu____78825
                                                               uu____78827
                                                           else ());
                                                          (let uu____78832 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____78832
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____78861)
                                                               ->
                                                               let uu____78874
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____78887
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____78887,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____78891
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____78891
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____78904
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____78904,
                                                                    decls0))
                                                                  in
                                                               (match uu____78874
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
                                                                    let uu____78925
                                                                    =
                                                                    let uu____78937
                                                                    =
                                                                    let uu____78940
                                                                    =
                                                                    let uu____78943
                                                                    =
                                                                    let uu____78946
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____78946
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____78943
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____78940
                                                                     in
                                                                    (g,
                                                                    uu____78937,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____78925
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
                                                                    let uu____78976
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____78976
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
                                                                    let uu____78991
                                                                    =
                                                                    let uu____78994
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____78994
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____78991
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____79000
                                                                    =
                                                                    let uu____79003
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____79003
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79000
                                                                     in
                                                                    let uu____79008
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____79008
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____79024
                                                                    =
                                                                    let uu____79032
                                                                    =
                                                                    let uu____79033
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79034
                                                                    =
                                                                    let uu____79050
                                                                    =
                                                                    let uu____79051
                                                                    =
                                                                    let uu____79056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79056)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79051
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79050)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79033
                                                                    uu____79034
                                                                     in
                                                                    let uu____79070
                                                                    =
                                                                    let uu____79071
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79071
                                                                     in
                                                                    (uu____79032,
                                                                    uu____79070,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79024
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79078
                                                                    =
                                                                    let uu____79086
                                                                    =
                                                                    let uu____79087
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79088
                                                                    =
                                                                    let uu____79099
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79099)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79087
                                                                    uu____79088
                                                                     in
                                                                    (uu____79086,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79078
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79113
                                                                    =
                                                                    let uu____79121
                                                                    =
                                                                    let uu____79122
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79123
                                                                    =
                                                                    let uu____79134
                                                                    =
                                                                    let uu____79135
                                                                    =
                                                                    let uu____79140
                                                                    =
                                                                    let uu____79141
                                                                    =
                                                                    let uu____79144
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79144
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79141
                                                                     in
                                                                    (gsapp,
                                                                    uu____79140)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79135
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79134)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79122
                                                                    uu____79123
                                                                     in
                                                                    (uu____79121,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79113
                                                                     in
                                                                    let uu____79158
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
                                                                    let uu____79170
                                                                    =
                                                                    let uu____79171
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79171
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79170
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79173
                                                                    =
                                                                    let uu____79181
                                                                    =
                                                                    let uu____79182
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79183
                                                                    =
                                                                    let uu____79194
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79194)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79182
                                                                    uu____79183
                                                                     in
                                                                    (uu____79181,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79173
                                                                     in
                                                                    let uu____79207
                                                                    =
                                                                    let uu____79216
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____79216
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____79231
                                                                    =
                                                                    let uu____79234
                                                                    =
                                                                    let uu____79235
                                                                    =
                                                                    let uu____79243
                                                                    =
                                                                    let uu____79244
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79245
                                                                    =
                                                                    let uu____79256
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79256)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79244
                                                                    uu____79245
                                                                     in
                                                                    (uu____79243,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79235
                                                                     in
                                                                    [uu____79234]
                                                                     in
                                                                    (d3,
                                                                    uu____79231)
                                                                     in
                                                                    match uu____79207
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79158
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____79313
                                                                    =
                                                                    let uu____79316
                                                                    =
                                                                    let uu____79319
                                                                    =
                                                                    let uu____79322
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____79322
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____79319
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____79316
                                                                     in
                                                                    let uu____79329
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____79313,
                                                                    uu____79329,
                                                                    env02))))))))))
                                      in
                                   let uu____79334 =
                                     let uu____79347 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____79410  ->
                                          fun uu____79411  ->
                                            match (uu____79410, uu____79411)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____79536 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____79536 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____79347
                                      in
                                   (match uu____79334 with
                                    | (decls2,eqns,env01) ->
                                        let uu____79603 =
                                          let isDeclFun uu___640_79620 =
                                            match uu___640_79620 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____79622 -> true
                                            | uu____79635 -> false  in
                                          let uu____79637 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____79637
                                            (fun decls3  ->
                                               let uu____79667 =
                                                 FStar_List.fold_left
                                                   (fun uu____79698  ->
                                                      fun elt  ->
                                                        match uu____79698
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____79739 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____79739
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____79767
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____79767
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
                                                                    let uu___1459_79805
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_79805.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_79805.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_79805.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____79667 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____79837 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____79837, elts, rest))
                                           in
                                        (match uu____79603 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____79866 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_79872  ->
                                        match uu___641_79872 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____79875 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____79883 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____79883)))
                                in
                             if uu____79866
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_79905  ->
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
                   let uu____79944 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____79944
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____79963 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____79963, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____80019 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____80019 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____80025 = encode_sigelt' env se  in
      match uu____80025 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80037 =
                  let uu____80040 =
                    let uu____80041 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80041  in
                  [uu____80040]  in
                FStar_All.pipe_right uu____80037
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80046 ->
                let uu____80047 =
                  let uu____80050 =
                    let uu____80053 =
                      let uu____80054 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80054  in
                    [uu____80053]  in
                  FStar_All.pipe_right uu____80050
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80061 =
                  let uu____80064 =
                    let uu____80067 =
                      let uu____80070 =
                        let uu____80071 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80071  in
                      [uu____80070]  in
                    FStar_All.pipe_right uu____80067
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80064  in
                FStar_List.append uu____80047 uu____80061
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80085 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80085
       then
         let uu____80090 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80090
       else ());
      (let is_opaque_to_smt t =
         let uu____80102 =
           let uu____80103 = FStar_Syntax_Subst.compress t  in
           uu____80103.FStar_Syntax_Syntax.n  in
         match uu____80102 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80108)) -> s = "opaque_to_smt"
         | uu____80113 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80122 =
           let uu____80123 = FStar_Syntax_Subst.compress t  in
           uu____80123.FStar_Syntax_Syntax.n  in
         match uu____80122 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80128)) -> s = "uninterpreted_by_smt"
         | uu____80133 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80139 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80145 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80157 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80158 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80159 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80172 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80174 =
             let uu____80176 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80176  in
           if uu____80174
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____80205 ->
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
                let uu____80237 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____80237 with
                | (formals,uu____80257) ->
                    let arity = FStar_List.length formals  in
                    let uu____80281 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____80281 with
                     | (aname,atok,env2) ->
                         let uu____80303 =
                           let uu____80308 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____80308 env2
                            in
                         (match uu____80303 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____80320 =
                                  let uu____80321 =
                                    let uu____80333 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____80353  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____80333,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____80321
                                   in
                                [uu____80320;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____80370 =
                                let aux uu____80416 uu____80417 =
                                  match (uu____80416, uu____80417) with
                                  | ((bv,uu____80461),(env3,acc_sorts,acc))
                                      ->
                                      let uu____80493 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____80493 with
                                       | (xxsym,xx,env4) ->
                                           let uu____80516 =
                                             let uu____80519 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____80519 :: acc_sorts  in
                                           (env4, uu____80516, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____80370 with
                               | (uu____80551,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____80567 =
                                       let uu____80575 =
                                         let uu____80576 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80577 =
                                           let uu____80588 =
                                             let uu____80589 =
                                               let uu____80594 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____80594)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____80589
                                              in
                                           ([[app]], xs_sorts, uu____80588)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80576 uu____80577
                                          in
                                       (uu____80575,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80567
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____80609 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____80609
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____80612 =
                                       let uu____80620 =
                                         let uu____80621 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____80622 =
                                           let uu____80633 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____80633)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____80621 uu____80622
                                          in
                                       (uu____80620,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____80612
                                      in
                                   let uu____80646 =
                                     let uu____80649 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____80649  in
                                   (env2, uu____80646))))
                 in
              let uu____80658 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____80658 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80684,uu____80685)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____80686 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____80686 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____80708,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____80715 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_80721  ->
                       match uu___642_80721 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____80724 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____80730 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____80733 -> false))
                in
             Prims.op_Negation uu____80715  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____80743 =
                let uu____80748 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____80748 env fv t quals  in
              match uu____80743 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____80762 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____80762  in
                  let uu____80765 =
                    let uu____80766 =
                      let uu____80769 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____80769
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____80766  in
                  (uu____80765, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____80779 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____80779 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_80791 = env  in
                  let uu____80792 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_80791.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_80791.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_80791.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____80792;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_80791.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_80791.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_80791.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_80791.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_80791.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_80791.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_80791.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____80794 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____80794 with
                 | (f3,decls) ->
                     let g =
                       let uu____80808 =
                         let uu____80811 =
                           let uu____80812 =
                             let uu____80820 =
                               let uu____80821 =
                                 let uu____80823 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____80823
                                  in
                               FStar_Pervasives_Native.Some uu____80821  in
                             let uu____80827 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____80820, uu____80827)  in
                           FStar_SMTEncoding_Util.mkAssume uu____80812  in
                         [uu____80811]  in
                       FStar_All.pipe_right uu____80808
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____80836) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____80850 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____80872 =
                        let uu____80875 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____80875.FStar_Syntax_Syntax.fv_name  in
                      uu____80872.FStar_Syntax_Syntax.v  in
                    let uu____80876 =
                      let uu____80878 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____80878  in
                    if uu____80876
                    then
                      let val_decl =
                        let uu___1629_80910 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_80910.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_80910.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_80910.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____80911 = encode_sigelt' env1 val_decl  in
                      match uu____80911 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____80850 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____80947,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____80949;
                           FStar_Syntax_Syntax.lbtyp = uu____80950;
                           FStar_Syntax_Syntax.lbeff = uu____80951;
                           FStar_Syntax_Syntax.lbdef = uu____80952;
                           FStar_Syntax_Syntax.lbattrs = uu____80953;
                           FStar_Syntax_Syntax.lbpos = uu____80954;_}::[]),uu____80955)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____80974 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____80974 with
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
                  let uu____81012 =
                    let uu____81015 =
                      let uu____81016 =
                        let uu____81024 =
                          let uu____81025 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____81026 =
                            let uu____81037 =
                              let uu____81038 =
                                let uu____81043 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81043)  in
                              FStar_SMTEncoding_Util.mkEq uu____81038  in
                            ([[b2t_x]], [xx], uu____81037)  in
                          FStar_SMTEncoding_Term.mkForall uu____81025
                            uu____81026
                           in
                        (uu____81024,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____81016  in
                    [uu____81015]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____81012
                   in
                let uu____81081 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81081, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81084,uu____81085) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81095  ->
                   match uu___643_81095 with
                   | FStar_Syntax_Syntax.Discriminator uu____81097 -> true
                   | uu____81099 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81101,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81113 =
                      let uu____81115 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81115.FStar_Ident.idText  in
                    uu____81113 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81122  ->
                      match uu___644_81122 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81125 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81128) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81142  ->
                   match uu___645_81142 with
                   | FStar_Syntax_Syntax.Projector uu____81144 -> true
                   | uu____81150 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81154 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81154 with
            | FStar_Pervasives_Native.Some uu____81161 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_81163 = se  in
                  let uu____81164 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81164;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_81163.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_81163.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_81163.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81167) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81182) ->
           let uu____81191 = encode_sigelts env ses  in
           (match uu____81191 with
            | (g,env1) ->
                let uu____81202 =
                  FStar_List.fold_left
                    (fun uu____81226  ->
                       fun elt  ->
                         match uu____81226 with
                         | (g',inversions) ->
                             let uu____81254 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_81277  ->
                                       match uu___646_81277 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____81279;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____81280;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____81281;_}
                                           -> false
                                       | uu____81288 -> true))
                                in
                             (match uu____81254 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_81313 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_81313.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_81313.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_81313.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____81202 with
                 | (g',inversions) ->
                     let uu____81332 =
                       FStar_List.fold_left
                         (fun uu____81363  ->
                            fun elt  ->
                              match uu____81363 with
                              | (decls,elts,rest) ->
                                  let uu____81404 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_81413  ->
                                            match uu___647_81413 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____81415 -> true
                                            | uu____81428 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____81404
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____81451 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_81472  ->
                                               match uu___648_81472 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____81474 -> true
                                               | uu____81487 -> false))
                                        in
                                     match uu____81451 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_81518 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_81518.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_81518.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_81518.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____81332 with
                      | (decls,elts,rest) ->
                          let uu____81544 =
                            let uu____81545 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____81552 =
                              let uu____81555 =
                                let uu____81558 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____81558  in
                              FStar_List.append elts uu____81555  in
                            FStar_List.append uu____81545 uu____81552  in
                          (uu____81544, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____81569,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____81582 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____81582 with
             | (usubst,uvs) ->
                 let uu____81602 =
                   let uu____81609 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____81610 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____81611 =
                     let uu____81612 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____81612 k  in
                   (uu____81609, uu____81610, uu____81611)  in
                 (match uu____81602 with
                  | (env1,tps1,k1) ->
                      let uu____81625 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____81625 with
                       | (tps2,k2) ->
                           let uu____81633 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____81633 with
                            | (uu____81649,k3) ->
                                let uu____81671 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____81671 with
                                 | (tps3,env_tps,uu____81683,us) ->
                                     let u_k =
                                       let uu____81686 =
                                         let uu____81687 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____81688 =
                                           let uu____81693 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____81695 =
                                             let uu____81696 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____81696
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____81693 uu____81695
                                            in
                                         uu____81688
                                           FStar_Pervasives_Native.None
                                           uu____81687
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____81686 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____81714) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____81720,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____81723) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____81731,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____81738) ->
                                           let uu____81739 =
                                             let uu____81741 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81741
                                              in
                                           failwith uu____81739
                                       | (uu____81745,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____81746 =
                                             let uu____81748 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81748
                                              in
                                           failwith uu____81746
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____81752,uu____81753) ->
                                           let uu____81762 =
                                             let uu____81764 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81764
                                              in
                                           failwith uu____81762
                                       | (uu____81768,FStar_Syntax_Syntax.U_unif
                                          uu____81769) ->
                                           let uu____81778 =
                                             let uu____81780 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____81780
                                              in
                                           failwith uu____81778
                                       | uu____81784 -> false  in
                                     let u_leq_u_k u =
                                       let uu____81797 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____81797 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81815 = u_leq_u_k u_tp  in
                                       if uu____81815
                                       then true
                                       else
                                         (let uu____81822 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____81822 with
                                          | (formals,uu____81839) ->
                                              let uu____81860 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____81860 with
                                               | (uu____81870,uu____81871,uu____81872,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____81883 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____81883
             then
               let uu____81888 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____81888
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_81908  ->
                       match uu___649_81908 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____81912 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____81925 = c  in
                 match uu____81925 with
                 | (name,args,uu____81930,uu____81931,uu____81932) ->
                     let uu____81943 =
                       let uu____81944 =
                         let uu____81956 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____81983  ->
                                   match uu____81983 with
                                   | (uu____81992,sort,uu____81994) -> sort))
                            in
                         (name, uu____81956,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____81944  in
                     [uu____81943]
               else
                 (let uu____82005 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____82005 c)
                in
             let inversion_axioms tapp vars =
               let uu____82023 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____82031 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____82031 FStar_Option.isNone))
                  in
               if uu____82023
               then []
               else
                 (let uu____82066 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82066 with
                  | (xxsym,xx) ->
                      let uu____82079 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82118  ->
                                fun l  ->
                                  match uu____82118 with
                                  | (out,decls) ->
                                      let uu____82138 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82138 with
                                       | (uu____82149,data_t) ->
                                           let uu____82151 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82151 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82195 =
                                                    let uu____82196 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82196.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82195 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82199,indices)
                                                      -> indices
                                                  | uu____82225 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____82255  ->
                                                            match uu____82255
                                                            with
                                                            | (x,uu____82263)
                                                                ->
                                                                let uu____82268
                                                                  =
                                                                  let uu____82269
                                                                    =
                                                                    let uu____82277
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____82277,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____82269
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____82268)
                                                       env)
                                                   in
                                                let uu____82282 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____82282 with
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
                                                                  let uu____82317
                                                                    =
                                                                    let uu____82322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____82322,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____82317)
                                                             vars indices1
                                                         else []  in
                                                       let uu____82325 =
                                                         let uu____82326 =
                                                           let uu____82331 =
                                                             let uu____82332
                                                               =
                                                               let uu____82337
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____82338
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____82337,
                                                                 uu____82338)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____82332
                                                              in
                                                           (out, uu____82331)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____82326
                                                          in
                                                       (uu____82325,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82079 with
                       | (data_ax,decls) ->
                           let uu____82353 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____82353 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____82370 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____82370 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____82377 =
                                    let uu____82385 =
                                      let uu____82386 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____82387 =
                                        let uu____82398 =
                                          let uu____82399 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____82401 =
                                            let uu____82404 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____82404 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____82399 uu____82401
                                           in
                                        let uu____82406 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____82398,
                                          uu____82406)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____82386 uu____82387
                                       in
                                    let uu____82415 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____82385,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____82415)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____82377
                                   in
                                let uu____82421 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____82421)))
                in
             let uu____82428 =
               let uu____82433 =
                 let uu____82434 = FStar_Syntax_Subst.compress k  in
                 uu____82434.FStar_Syntax_Syntax.n  in
               match uu____82433 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____82469 -> (tps, k)  in
             match uu____82428 with
             | (formals,res) ->
                 let uu____82476 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____82476 with
                  | (formals1,res1) ->
                      let uu____82487 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____82487 with
                       | (vars,guards,env',binder_decls,uu____82512) ->
                           let arity = FStar_List.length vars  in
                           let uu____82526 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____82526 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____82552 =
                                    let uu____82560 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____82560)  in
                                  FStar_SMTEncoding_Util.mkApp uu____82552
                                   in
                                let uu____82566 =
                                  let tname_decl =
                                    let uu____82576 =
                                      let uu____82577 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____82596 =
                                                  let uu____82598 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____82598
                                                   in
                                                let uu____82600 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____82596, uu____82600,
                                                  false)))
                                         in
                                      let uu____82604 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____82577,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____82604, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____82576
                                     in
                                  let uu____82612 =
                                    match vars with
                                    | [] ->
                                        let uu____82625 =
                                          let uu____82626 =
                                            let uu____82629 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _82635  ->
                                                 FStar_Pervasives_Native.Some
                                                   _82635) uu____82629
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____82626
                                           in
                                        ([], uu____82625)
                                    | uu____82638 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____82648 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____82648
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____82664 =
                                            let uu____82672 =
                                              let uu____82673 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____82674 =
                                                let uu____82690 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____82690)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____82673 uu____82674
                                               in
                                            (uu____82672,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____82664
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____82612 with
                                  | (tok_decls,env2) ->
                                      let uu____82717 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____82717
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____82566 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____82745 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____82745 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____82767 =
                                                 let uu____82768 =
                                                   let uu____82776 =
                                                     let uu____82777 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____82777
                                                      in
                                                   (uu____82776,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____82768
                                                  in
                                               [uu____82767]
                                             else []  in
                                           let uu____82785 =
                                             let uu____82788 =
                                               let uu____82791 =
                                                 let uu____82794 =
                                                   let uu____82795 =
                                                     let uu____82803 =
                                                       let uu____82804 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____82805 =
                                                         let uu____82816 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____82816)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____82804
                                                         uu____82805
                                                        in
                                                     (uu____82803,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____82795
                                                    in
                                                 [uu____82794]  in
                                               FStar_List.append karr
                                                 uu____82791
                                                in
                                             FStar_All.pipe_right uu____82788
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____82785
                                        in
                                     let aux =
                                       let uu____82835 =
                                         let uu____82838 =
                                           inversion_axioms tapp vars  in
                                         let uu____82841 =
                                           let uu____82844 =
                                             let uu____82847 =
                                               let uu____82848 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____82848 env2
                                                 tapp vars
                                                in
                                             [uu____82847]  in
                                           FStar_All.pipe_right uu____82844
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____82838
                                           uu____82841
                                          in
                                       FStar_List.append kindingAx
                                         uu____82835
                                        in
                                     let g =
                                       let uu____82856 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____82856
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82864,uu____82865,uu____82866,uu____82867,uu____82868)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____82876,t,uu____82878,n_tps,uu____82880) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____82890 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____82890 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____82938 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____82938 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____82962 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____82962 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____82982 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____82982 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83061 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83061,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83068 =
                                   let uu____83069 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83069, true)
                                    in
                                 let uu____83077 =
                                   let uu____83084 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83084
                                    in
                                 FStar_All.pipe_right uu____83068 uu____83077
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
                               let uu____83096 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____83096 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83108::uu____83109 ->
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
                                            let uu____83158 =
                                              let uu____83159 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83159]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83158
                                             in
                                          let uu____83185 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83186 =
                                            let uu____83197 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83197)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83185 uu____83186
                                      | uu____83224 -> tok_typing  in
                                    let uu____83235 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____83235 with
                                     | (vars',guards',env'',decls_formals,uu____83260)
                                         ->
                                         let uu____83273 =
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
                                         (match uu____83273 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____83303 ->
                                                    let uu____83312 =
                                                      let uu____83313 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____83313
                                                       in
                                                    [uu____83312]
                                                 in
                                              let encode_elim uu____83329 =
                                                let uu____83330 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____83330 with
                                                | (head1,args) ->
                                                    let uu____83381 =
                                                      let uu____83382 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____83382.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____83381 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____83394;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____83395;_},uu____83396)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____83402 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____83402
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
                                                                  | uu____83465
                                                                    ->
                                                                    let uu____83466
                                                                    =
                                                                    let uu____83472
                                                                    =
                                                                    let uu____83474
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____83474
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____83472)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____83466
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____83497
                                                                    =
                                                                    let uu____83499
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____83499
                                                                     in
                                                                    if
                                                                    uu____83497
                                                                    then
                                                                    let uu____83521
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____83521]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____83524
                                                                =
                                                                let uu____83538
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____83595
                                                                     ->
                                                                    fun
                                                                    uu____83596
                                                                     ->
                                                                    match 
                                                                    (uu____83595,
                                                                    uu____83596)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____83707
                                                                    =
                                                                    let uu____83715
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____83715
                                                                     in
                                                                    (match uu____83707
                                                                    with
                                                                    | 
                                                                    (uu____83729,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____83740
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____83740
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____83745
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____83745
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
                                                                  uu____83538
                                                                 in
                                                              (match uu____83524
                                                               with
                                                               | (uu____83766,arg_vars,elim_eqns_or_guards,uu____83769)
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
                                                                    let uu____83796
                                                                    =
                                                                    let uu____83804
                                                                    =
                                                                    let uu____83805
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83806
                                                                    =
                                                                    let uu____83817
                                                                    =
                                                                    let uu____83818
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83818
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83820
                                                                    =
                                                                    let uu____83821
                                                                    =
                                                                    let uu____83826
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____83826)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83821
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83817,
                                                                    uu____83820)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83805
                                                                    uu____83806
                                                                     in
                                                                    (uu____83804,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83796
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____83841
                                                                    =
                                                                    let uu____83842
                                                                    =
                                                                    let uu____83848
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____83848,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83842
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____83841
                                                                     in
                                                                    let uu____83851
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____83851
                                                                    then
                                                                    let x =
                                                                    let uu____83855
                                                                    =
                                                                    let uu____83861
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____83861,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____83855
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____83866
                                                                    =
                                                                    let uu____83874
                                                                    =
                                                                    let uu____83875
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83876
                                                                    =
                                                                    let uu____83887
                                                                    =
                                                                    let uu____83892
                                                                    =
                                                                    let uu____83895
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____83895]
                                                                     in
                                                                    [uu____83892]
                                                                     in
                                                                    let uu____83900
                                                                    =
                                                                    let uu____83901
                                                                    =
                                                                    let uu____83906
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____83908
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____83906,
                                                                    uu____83908)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83901
                                                                     in
                                                                    (uu____83887,
                                                                    [x],
                                                                    uu____83900)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83875
                                                                    uu____83876
                                                                     in
                                                                    let uu____83929
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____83874,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____83929)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83866
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____83940
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
                                                                    (let uu____83963
                                                                    =
                                                                    let uu____83964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____83964
                                                                    dapp1  in
                                                                    [uu____83963])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83940
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____83971
                                                                    =
                                                                    let uu____83979
                                                                    =
                                                                    let uu____83980
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____83981
                                                                    =
                                                                    let uu____83992
                                                                    =
                                                                    let uu____83993
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____83993
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____83995
                                                                    =
                                                                    let uu____83996
                                                                    =
                                                                    let uu____84001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84001)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83996
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____83992,
                                                                    uu____83995)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83980
                                                                    uu____83981
                                                                     in
                                                                    (uu____83979,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83971)
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
                                                         let uu____84020 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84020
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
                                                                  | uu____84083
                                                                    ->
                                                                    let uu____84084
                                                                    =
                                                                    let uu____84090
                                                                    =
                                                                    let uu____84092
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84092
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84090)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84084
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84115
                                                                    =
                                                                    let uu____84117
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84117
                                                                     in
                                                                    if
                                                                    uu____84115
                                                                    then
                                                                    let uu____84139
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84139]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84142
                                                                =
                                                                let uu____84156
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84213
                                                                     ->
                                                                    fun
                                                                    uu____84214
                                                                     ->
                                                                    match 
                                                                    (uu____84213,
                                                                    uu____84214)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84325
                                                                    =
                                                                    let uu____84333
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84333
                                                                     in
                                                                    (match uu____84325
                                                                    with
                                                                    | 
                                                                    (uu____84347,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84358
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84358
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84363
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84363
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
                                                                  uu____84156
                                                                 in
                                                              (match uu____84142
                                                               with
                                                               | (uu____84384,arg_vars,elim_eqns_or_guards,uu____84387)
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
                                                                    let uu____84414
                                                                    =
                                                                    let uu____84422
                                                                    =
                                                                    let uu____84423
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84424
                                                                    =
                                                                    let uu____84435
                                                                    =
                                                                    let uu____84436
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84436
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84438
                                                                    =
                                                                    let uu____84439
                                                                    =
                                                                    let uu____84444
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84444)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84439
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84435,
                                                                    uu____84438)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84423
                                                                    uu____84424
                                                                     in
                                                                    (uu____84422,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84414
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84459
                                                                    =
                                                                    let uu____84460
                                                                    =
                                                                    let uu____84466
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84466,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84460
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84459
                                                                     in
                                                                    let uu____84469
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84469
                                                                    then
                                                                    let x =
                                                                    let uu____84473
                                                                    =
                                                                    let uu____84479
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84479,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84473
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84484
                                                                    =
                                                                    let uu____84492
                                                                    =
                                                                    let uu____84493
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84494
                                                                    =
                                                                    let uu____84505
                                                                    =
                                                                    let uu____84510
                                                                    =
                                                                    let uu____84513
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84513]
                                                                     in
                                                                    [uu____84510]
                                                                     in
                                                                    let uu____84518
                                                                    =
                                                                    let uu____84519
                                                                    =
                                                                    let uu____84524
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84524,
                                                                    uu____84526)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84519
                                                                     in
                                                                    (uu____84505,
                                                                    [x],
                                                                    uu____84518)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84493
                                                                    uu____84494
                                                                     in
                                                                    let uu____84547
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84492,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84547)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84484
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84558
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
                                                                    (let uu____84581
                                                                    =
                                                                    let uu____84582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84582
                                                                    dapp1  in
                                                                    [uu____84581])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84558
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____84589
                                                                    =
                                                                    let uu____84597
                                                                    =
                                                                    let uu____84598
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84599
                                                                    =
                                                                    let uu____84610
                                                                    =
                                                                    let uu____84611
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84611
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84613
                                                                    =
                                                                    let uu____84614
                                                                    =
                                                                    let uu____84619
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84619)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84614
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84610,
                                                                    uu____84613)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84598
                                                                    uu____84599
                                                                     in
                                                                    (uu____84597,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84589)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____84636 ->
                                                         ((let uu____84638 =
                                                             let uu____84644
                                                               =
                                                               let uu____84646
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____84648
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____84646
                                                                 uu____84648
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____84644)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____84638);
                                                          ([], [])))
                                                 in
                                              let uu____84656 =
                                                encode_elim ()  in
                                              (match uu____84656 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____84682 =
                                                       let uu____84685 =
                                                         let uu____84688 =
                                                           let uu____84691 =
                                                             let uu____84694
                                                               =
                                                               let uu____84697
                                                                 =
                                                                 let uu____84700
                                                                   =
                                                                   let uu____84701
                                                                    =
                                                                    let uu____84713
                                                                    =
                                                                    let uu____84714
                                                                    =
                                                                    let uu____84716
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____84716
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84714
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____84713)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____84701
                                                                    in
                                                                 [uu____84700]
                                                                  in
                                                               FStar_List.append
                                                                 uu____84697
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____84694
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____84727 =
                                                             let uu____84730
                                                               =
                                                               let uu____84733
                                                                 =
                                                                 let uu____84736
                                                                   =
                                                                   let uu____84739
                                                                    =
                                                                    let uu____84742
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____84747
                                                                    =
                                                                    let uu____84750
                                                                    =
                                                                    let uu____84751
                                                                    =
                                                                    let uu____84759
                                                                    =
                                                                    let uu____84760
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84761
                                                                    =
                                                                    let uu____84772
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84772)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84760
                                                                    uu____84761
                                                                     in
                                                                    (uu____84759,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84751
                                                                     in
                                                                    let uu____84785
                                                                    =
                                                                    let uu____84788
                                                                    =
                                                                    let uu____84789
                                                                    =
                                                                    let uu____84797
                                                                    =
                                                                    let uu____84798
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84799
                                                                    =
                                                                    let uu____84810
                                                                    =
                                                                    let uu____84811
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84811
                                                                    vars'  in
                                                                    let uu____84813
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____84810,
                                                                    uu____84813)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84798
                                                                    uu____84799
                                                                     in
                                                                    (uu____84797,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84789
                                                                     in
                                                                    [uu____84788]
                                                                     in
                                                                    uu____84750
                                                                    ::
                                                                    uu____84785
                                                                     in
                                                                    uu____84742
                                                                    ::
                                                                    uu____84747
                                                                     in
                                                                   FStar_List.append
                                                                    uu____84739
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____84736
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____84733
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____84730
                                                              in
                                                           FStar_List.append
                                                             uu____84691
                                                             uu____84727
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____84688
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____84685
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____84682
                                                      in
                                                   let uu____84830 =
                                                     let uu____84831 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____84831 g
                                                      in
                                                   (uu____84830, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____84865  ->
              fun se  ->
                match uu____84865 with
                | (g,env1) ->
                    let uu____84885 = encode_sigelt env1 se  in
                    (match uu____84885 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____84953 =
        match uu____84953 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____84990 ->
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
                 ((let uu____84998 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____84998
                   then
                     let uu____85003 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____85005 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____85007 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____85003 uu____85005 uu____85007
                   else ());
                  (let uu____85012 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____85012 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____85030 =
                         let uu____85038 =
                           let uu____85040 =
                             let uu____85042 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85042
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85040  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85038
                          in
                       (match uu____85030 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85062 = FStar_Options.log_queries ()
                                 in
                              if uu____85062
                              then
                                let uu____85065 =
                                  let uu____85067 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85069 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85071 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85067 uu____85069 uu____85071
                                   in
                                FStar_Pervasives_Native.Some uu____85065
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85087 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85097 =
                                let uu____85100 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85100  in
                              FStar_List.append uu____85087 uu____85097  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85112,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85132 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85132 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85153 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85153 with | (uu____85180,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____85233  ->
              match uu____85233 with
              | (l,uu____85242,uu____85243) ->
                  let uu____85246 =
                    let uu____85258 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____85258, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____85246))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____85291  ->
              match uu____85291 with
              | (l,uu____85302,uu____85303) ->
                  let uu____85306 =
                    let uu____85307 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _85310  -> FStar_SMTEncoding_Term.Echo _85310)
                      uu____85307
                     in
                  let uu____85311 =
                    let uu____85314 =
                      let uu____85315 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____85315  in
                    [uu____85314]  in
                  uu____85306 :: uu____85311))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____85333 =
      let uu____85336 =
        let uu____85337 = FStar_Util.psmap_empty ()  in
        let uu____85352 =
          let uu____85361 = FStar_Util.psmap_empty ()  in (uu____85361, [])
           in
        let uu____85368 =
          let uu____85370 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____85370 FStar_Ident.string_of_lid  in
        let uu____85372 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____85337;
          FStar_SMTEncoding_Env.fvar_bindings = uu____85352;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____85368;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____85372
        }  in
      [uu____85336]  in
    FStar_ST.op_Colon_Equals last_env uu____85333
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____85416 = FStar_ST.op_Bang last_env  in
      match uu____85416 with
      | [] -> failwith "No env; call init first!"
      | e::uu____85444 ->
          let uu___2175_85447 = e  in
          let uu____85448 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_85447.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_85447.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_85447.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_85447.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_85447.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_85447.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_85447.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____85448;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_85447.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_85447.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____85456 = FStar_ST.op_Bang last_env  in
    match uu____85456 with
    | [] -> failwith "Empty env stack"
    | uu____85483::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____85515  ->
    let uu____85516 = FStar_ST.op_Bang last_env  in
    match uu____85516 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____85576  ->
    let uu____85577 = FStar_ST.op_Bang last_env  in
    match uu____85577 with
    | [] -> failwith "Popping an empty stack"
    | uu____85604::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____85641  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____85694  ->
         let uu____85695 = snapshot_env ()  in
         match uu____85695 with
         | (env_depth,()) ->
             let uu____85717 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____85717 with
              | (varops_depth,()) ->
                  let uu____85739 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____85739 with
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
        (fun uu____85797  ->
           let uu____85798 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____85798 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____85893 = snapshot msg  in () 
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
        | (uu____85939::uu____85940,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_85948 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_85948.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_85948.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_85948.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____85949 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_85976 = elt  in
        let uu____85977 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_85976.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_85976.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____85977;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_85976.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____85997 =
        let uu____86000 =
          let uu____86001 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____86001  in
        let uu____86002 = open_fact_db_tags env  in uu____86000 ::
          uu____86002
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____85997
  
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
      let uu____86029 = encode_sigelt env se  in
      match uu____86029 with
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
                (let uu____86075 =
                   let uu____86078 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86078
                    in
                 match uu____86075 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86093 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86093
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86123 = FStar_Options.log_queries ()  in
        if uu____86123
        then
          let uu____86128 =
            let uu____86129 =
              let uu____86131 =
                let uu____86133 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86133 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86131  in
            FStar_SMTEncoding_Term.Caption uu____86129  in
          uu____86128 :: decls
        else decls  in
      (let uu____86152 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86152
       then
         let uu____86155 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86155
       else ());
      (let env =
         let uu____86161 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86161 tcenv  in
       let uu____86162 = encode_top_level_facts env se  in
       match uu____86162 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86176 =
               let uu____86179 =
                 let uu____86182 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86182
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86179  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86176)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____86215 = FStar_Options.log_queries ()  in
          if uu____86215
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_86235 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_86235.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_86235.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_86235.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_86235.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_86235.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_86235.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_86235.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_86235.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_86235.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_86235.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____86240 =
             let uu____86243 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____86243
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____86240  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____86263 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____86263
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
          (let uu____86287 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____86287
           then
             let uu____86290 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____86290
           else ());
          (let env =
             let uu____86298 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____86298
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____86337  ->
                     fun se  ->
                       match uu____86337 with
                       | (g,env2) ->
                           let uu____86357 = encode_top_level_facts env2 se
                              in
                           (match uu____86357 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____86380 =
             encode_signature
               (let uu___2303_86389 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_86389.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_86389.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_86389.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_86389.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_86389.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_86389.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_86389.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_86389.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_86389.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_86389.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____86380 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____86405 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86405
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____86411 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____86411))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____86439  ->
        match uu____86439 with
        | (decls,fvbs) ->
            ((let uu____86453 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____86453
              then ()
              else
                (let uu____86458 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____86458
                 then
                   let uu____86461 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____86461
                 else ()));
             (let env =
                let uu____86469 = get_env name tcenv  in
                FStar_All.pipe_right uu____86469
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____86471 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____86471
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____86485 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____86485
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
        (let uu____86547 =
           let uu____86549 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____86549.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____86547);
        (let env =
           let uu____86551 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____86551 tcenv  in
         let uu____86552 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____86591 = aux rest  in
                 (match uu____86591 with
                  | (out,rest1) ->
                      let t =
                        let uu____86619 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____86619 with
                        | FStar_Pervasives_Native.Some uu____86622 ->
                            let uu____86623 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____86623
                              x.FStar_Syntax_Syntax.sort
                        | uu____86624 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____86628 =
                        let uu____86631 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_86634 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_86634.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_86634.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____86631 :: out  in
                      (uu____86628, rest1))
             | uu____86639 -> ([], bindings)  in
           let uu____86646 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____86646 with
           | (closing,bindings) ->
               let uu____86673 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____86673, bindings)
            in
         match uu____86552 with
         | (q1,bindings) ->
             let uu____86704 = encode_env_bindings env bindings  in
             (match uu____86704 with
              | (env_decls,env1) ->
                  ((let uu____86726 =
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
                    if uu____86726
                    then
                      let uu____86733 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____86733
                    else ());
                   (let uu____86738 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____86738 with
                    | (phi,qdecls) ->
                        let uu____86759 =
                          let uu____86764 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____86764 phi
                           in
                        (match uu____86759 with
                         | (labels,phi1) ->
                             let uu____86781 = encode_labels labels  in
                             (match uu____86781 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____86817 =
                                      FStar_Options.log_queries ()  in
                                    if uu____86817
                                    then
                                      let uu____86822 =
                                        let uu____86823 =
                                          let uu____86825 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____86825
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____86823
                                         in
                                      [uu____86822]
                                    else []  in
                                  let query_prelude =
                                    let uu____86833 =
                                      let uu____86834 =
                                        let uu____86835 =
                                          let uu____86838 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____86845 =
                                            let uu____86848 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____86848
                                             in
                                          FStar_List.append uu____86838
                                            uu____86845
                                           in
                                        FStar_List.append env_decls
                                          uu____86835
                                         in
                                      FStar_All.pipe_right uu____86834
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____86833
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____86858 =
                                      let uu____86866 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____86867 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____86866,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____86867)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____86858
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
  