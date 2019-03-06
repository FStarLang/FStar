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
  let uu____72871 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72871 with
  | (asym,a) ->
      let uu____72882 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72882 with
       | (xsym,x) ->
           let uu____72893 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72893 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72971 =
                      let uu____72983 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72983, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72971  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____73003 =
                      let uu____73011 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____73011)  in
                    FStar_SMTEncoding_Util.mkApp uu____73003  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____73030 =
                    let uu____73033 =
                      let uu____73036 =
                        let uu____73039 =
                          let uu____73040 =
                            let uu____73048 =
                              let uu____73049 =
                                let uu____73060 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____73060)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____73049
                               in
                            (uu____73048, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____73040  in
                        let uu____73072 =
                          let uu____73075 =
                            let uu____73076 =
                              let uu____73084 =
                                let uu____73085 =
                                  let uu____73096 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____73096)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____73085
                                 in
                              (uu____73084,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____73076  in
                          [uu____73075]  in
                        uu____73039 :: uu____73072  in
                      xtok_decl :: uu____73036  in
                    xname_decl :: uu____73033  in
                  (xtok1, (FStar_List.length vars), uu____73030)  in
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
                  let uu____73266 =
                    let uu____73287 =
                      let uu____73306 =
                        let uu____73307 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73307
                         in
                      quant axy uu____73306  in
                    (FStar_Parser_Const.op_Eq, uu____73287)  in
                  let uu____73324 =
                    let uu____73347 =
                      let uu____73368 =
                        let uu____73387 =
                          let uu____73388 =
                            let uu____73389 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73389  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73388
                           in
                        quant axy uu____73387  in
                      (FStar_Parser_Const.op_notEq, uu____73368)  in
                    let uu____73406 =
                      let uu____73429 =
                        let uu____73450 =
                          let uu____73469 =
                            let uu____73470 =
                              let uu____73471 =
                                let uu____73476 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73477 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73476, uu____73477)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73471  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73470
                             in
                          quant xy uu____73469  in
                        (FStar_Parser_Const.op_And, uu____73450)  in
                      let uu____73494 =
                        let uu____73517 =
                          let uu____73538 =
                            let uu____73557 =
                              let uu____73558 =
                                let uu____73559 =
                                  let uu____73564 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73565 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73564, uu____73565)  in
                                FStar_SMTEncoding_Util.mkOr uu____73559  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73558
                               in
                            quant xy uu____73557  in
                          (FStar_Parser_Const.op_Or, uu____73538)  in
                        let uu____73582 =
                          let uu____73605 =
                            let uu____73626 =
                              let uu____73645 =
                                let uu____73646 =
                                  let uu____73647 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73647
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73646
                                 in
                              quant qx uu____73645  in
                            (FStar_Parser_Const.op_Negation, uu____73626)  in
                          let uu____73664 =
                            let uu____73687 =
                              let uu____73708 =
                                let uu____73727 =
                                  let uu____73728 =
                                    let uu____73729 =
                                      let uu____73734 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73735 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73734, uu____73735)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73729
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73728
                                   in
                                quant xy uu____73727  in
                              (FStar_Parser_Const.op_LT, uu____73708)  in
                            let uu____73752 =
                              let uu____73775 =
                                let uu____73796 =
                                  let uu____73815 =
                                    let uu____73816 =
                                      let uu____73817 =
                                        let uu____73822 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73823 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73822, uu____73823)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73817
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73816
                                     in
                                  quant xy uu____73815  in
                                (FStar_Parser_Const.op_LTE, uu____73796)  in
                              let uu____73840 =
                                let uu____73863 =
                                  let uu____73884 =
                                    let uu____73903 =
                                      let uu____73904 =
                                        let uu____73905 =
                                          let uu____73910 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73911 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73910, uu____73911)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73905
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73904
                                       in
                                    quant xy uu____73903  in
                                  (FStar_Parser_Const.op_GT, uu____73884)  in
                                let uu____73928 =
                                  let uu____73951 =
                                    let uu____73972 =
                                      let uu____73991 =
                                        let uu____73992 =
                                          let uu____73993 =
                                            let uu____73998 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73999 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73998, uu____73999)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73993
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73992
                                         in
                                      quant xy uu____73991  in
                                    (FStar_Parser_Const.op_GTE, uu____73972)
                                     in
                                  let uu____74016 =
                                    let uu____74039 =
                                      let uu____74060 =
                                        let uu____74079 =
                                          let uu____74080 =
                                            let uu____74081 =
                                              let uu____74086 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____74087 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____74086, uu____74087)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____74081
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____74080
                                           in
                                        quant xy uu____74079  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____74060)
                                       in
                                    let uu____74104 =
                                      let uu____74127 =
                                        let uu____74148 =
                                          let uu____74167 =
                                            let uu____74168 =
                                              let uu____74169 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74169
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74168
                                             in
                                          quant qx uu____74167  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74148)
                                         in
                                      let uu____74186 =
                                        let uu____74209 =
                                          let uu____74230 =
                                            let uu____74249 =
                                              let uu____74250 =
                                                let uu____74251 =
                                                  let uu____74256 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74257 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74256, uu____74257)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74251
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74250
                                               in
                                            quant xy uu____74249  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74230)
                                           in
                                        let uu____74274 =
                                          let uu____74297 =
                                            let uu____74318 =
                                              let uu____74337 =
                                                let uu____74338 =
                                                  let uu____74339 =
                                                    let uu____74344 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74345 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74344,
                                                      uu____74345)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74339
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74338
                                                 in
                                              quant xy uu____74337  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74318)
                                             in
                                          let uu____74362 =
                                            let uu____74385 =
                                              let uu____74406 =
                                                let uu____74425 =
                                                  let uu____74426 =
                                                    let uu____74427 =
                                                      let uu____74432 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74433 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74432,
                                                        uu____74433)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74427
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74426
                                                   in
                                                quant xy uu____74425  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74406)
                                               in
                                            let uu____74450 =
                                              let uu____74473 =
                                                let uu____74494 =
                                                  let uu____74513 =
                                                    let uu____74514 =
                                                      let uu____74515 =
                                                        let uu____74520 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74521 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74520,
                                                          uu____74521)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74515
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74514
                                                     in
                                                  quant xy uu____74513  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74494)
                                                 in
                                              let uu____74538 =
                                                let uu____74561 =
                                                  let uu____74582 =
                                                    let uu____74601 =
                                                      let uu____74602 =
                                                        let uu____74603 =
                                                          let uu____74608 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74609 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74608,
                                                            uu____74609)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74603
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74602
                                                       in
                                                    quant xy uu____74601  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74582)
                                                   in
                                                let uu____74626 =
                                                  let uu____74649 =
                                                    let uu____74670 =
                                                      let uu____74689 =
                                                        let uu____74690 =
                                                          let uu____74691 =
                                                            let uu____74696 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74697 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74696,
                                                              uu____74697)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74691
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74690
                                                         in
                                                      quant xy uu____74689
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74670)
                                                     in
                                                  let uu____74714 =
                                                    let uu____74737 =
                                                      let uu____74758 =
                                                        let uu____74777 =
                                                          let uu____74778 =
                                                            let uu____74779 =
                                                              let uu____74784
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74785
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74784,
                                                                uu____74785)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74779
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74778
                                                           in
                                                        quant xy uu____74777
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74758)
                                                       in
                                                    let uu____74802 =
                                                      let uu____74825 =
                                                        let uu____74846 =
                                                          let uu____74865 =
                                                            let uu____74866 =
                                                              let uu____74867
                                                                =
                                                                let uu____74872
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74873
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74872,
                                                                  uu____74873)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74867
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74866
                                                             in
                                                          quant xy
                                                            uu____74865
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74846)
                                                         in
                                                      let uu____74890 =
                                                        let uu____74913 =
                                                          let uu____74934 =
                                                            let uu____74953 =
                                                              let uu____74954
                                                                =
                                                                let uu____74955
                                                                  =
                                                                  let uu____74960
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74961
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74960,
                                                                    uu____74961)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74955
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74954
                                                               in
                                                            quant xy
                                                              uu____74953
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74934)
                                                           in
                                                        let uu____74978 =
                                                          let uu____75001 =
                                                            let uu____75022 =
                                                              let uu____75041
                                                                =
                                                                let uu____75042
                                                                  =
                                                                  let uu____75043
                                                                    =
                                                                    let uu____75048
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75049
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75048,
                                                                    uu____75049)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____75043
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____75042
                                                                 in
                                                              quant xy
                                                                uu____75041
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____75022)
                                                             in
                                                          let uu____75066 =
                                                            let uu____75089 =
                                                              let uu____75110
                                                                =
                                                                let uu____75129
                                                                  =
                                                                  let uu____75130
                                                                    =
                                                                    let uu____75131
                                                                    =
                                                                    let uu____75136
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75137
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75136,
                                                                    uu____75137)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75131
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75130
                                                                   in
                                                                quant xy
                                                                  uu____75129
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75110)
                                                               in
                                                            let uu____75154 =
                                                              let uu____75177
                                                                =
                                                                let uu____75198
                                                                  =
                                                                  let uu____75217
                                                                    =
                                                                    let uu____75218
                                                                    =
                                                                    let uu____75219
                                                                    =
                                                                    let uu____75224
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75225
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75224,
                                                                    uu____75225)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75219
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75218
                                                                     in
                                                                  quant xy
                                                                    uu____75217
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75198)
                                                                 in
                                                              let uu____75242
                                                                =
                                                                let uu____75265
                                                                  =
                                                                  let uu____75286
                                                                    =
                                                                    let uu____75305
                                                                    =
                                                                    let uu____75306
                                                                    =
                                                                    let uu____75307
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75307
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75306
                                                                     in
                                                                    quant qx
                                                                    uu____75305
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75286)
                                                                   in
                                                                [uu____75265]
                                                                 in
                                                              uu____75177 ::
                                                                uu____75242
                                                               in
                                                            uu____75089 ::
                                                              uu____75154
                                                             in
                                                          uu____75001 ::
                                                            uu____75066
                                                           in
                                                        uu____74913 ::
                                                          uu____74978
                                                         in
                                                      uu____74825 ::
                                                        uu____74890
                                                       in
                                                    uu____74737 ::
                                                      uu____74802
                                                     in
                                                  uu____74649 :: uu____74714
                                                   in
                                                uu____74561 :: uu____74626
                                                 in
                                              uu____74473 :: uu____74538  in
                                            uu____74385 :: uu____74450  in
                                          uu____74297 :: uu____74362  in
                                        uu____74209 :: uu____74274  in
                                      uu____74127 :: uu____74186  in
                                    uu____74039 :: uu____74104  in
                                  uu____73951 :: uu____74016  in
                                uu____73863 :: uu____73928  in
                              uu____73775 :: uu____73840  in
                            uu____73687 :: uu____73752  in
                          uu____73605 :: uu____73664  in
                        uu____73517 :: uu____73582  in
                      uu____73429 :: uu____73494  in
                    uu____73347 :: uu____73406  in
                  uu____73266 :: uu____73324  in
                let mk1 l v1 =
                  let uu____75846 =
                    let uu____75858 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75948  ->
                              match uu____75948 with
                              | (l',uu____75969) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75858
                      (FStar_Option.map
                         (fun uu____76068  ->
                            match uu____76068 with
                            | (uu____76096,b) ->
                                let uu____76130 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76130 v1))
                     in
                  FStar_All.pipe_right uu____75846 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76213  ->
                          match uu____76213 with
                          | (l',uu____76234) -> FStar_Ident.lid_equals l l'))
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
          let uu____76308 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76308 with
          | (xxsym,xx) ->
              let uu____76319 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76319 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76335 =
                     let uu____76343 =
                       let uu____76344 =
                         let uu____76355 =
                           let uu____76356 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76366 =
                             let uu____76377 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76377 :: vars  in
                           uu____76356 :: uu____76366  in
                         let uu____76403 =
                           let uu____76404 =
                             let uu____76409 =
                               let uu____76410 =
                                 let uu____76415 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76415)  in
                               FStar_SMTEncoding_Util.mkEq uu____76410  in
                             (xx_has_type, uu____76409)  in
                           FStar_SMTEncoding_Util.mkImp uu____76404  in
                         ([[xx_has_type]], uu____76355, uu____76403)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76344  in
                     let uu____76428 =
                       let uu____76430 =
                         let uu____76432 =
                           let uu____76434 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76434  in
                         Prims.op_Hat module_name uu____76432  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76430
                        in
                     (uu____76343,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76428)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76335)
  
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
    let uu____76490 =
      let uu____76492 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76492  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76490  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76514 =
      let uu____76515 =
        let uu____76523 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76523, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76515  in
    let uu____76528 =
      let uu____76531 =
        let uu____76532 =
          let uu____76540 =
            let uu____76541 =
              let uu____76552 =
                let uu____76553 =
                  let uu____76558 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76558)  in
                FStar_SMTEncoding_Util.mkImp uu____76553  in
              ([[typing_pred]], [xx], uu____76552)  in
            let uu____76583 =
              let uu____76598 = FStar_TypeChecker_Env.get_range env  in
              let uu____76599 = mkForall_fuel1 env  in
              uu____76599 uu____76598  in
            uu____76583 uu____76541  in
          (uu____76540, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76532  in
      [uu____76531]  in
    uu____76514 :: uu____76528  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76646 =
      let uu____76647 =
        let uu____76655 =
          let uu____76656 = FStar_TypeChecker_Env.get_range env  in
          let uu____76657 =
            let uu____76668 =
              let uu____76673 =
                let uu____76676 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76676]  in
              [uu____76673]  in
            let uu____76681 =
              let uu____76682 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76682 tt  in
            (uu____76668, [bb], uu____76681)  in
          FStar_SMTEncoding_Term.mkForall uu____76656 uu____76657  in
        (uu____76655, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76647  in
    let uu____76707 =
      let uu____76710 =
        let uu____76711 =
          let uu____76719 =
            let uu____76720 =
              let uu____76731 =
                let uu____76732 =
                  let uu____76737 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76737)  in
                FStar_SMTEncoding_Util.mkImp uu____76732  in
              ([[typing_pred]], [xx], uu____76731)  in
            let uu____76764 =
              let uu____76779 = FStar_TypeChecker_Env.get_range env  in
              let uu____76780 = mkForall_fuel1 env  in
              uu____76780 uu____76779  in
            uu____76764 uu____76720  in
          (uu____76719, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76711  in
      [uu____76710]  in
    uu____76646 :: uu____76707  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76823 =
        let uu____76824 =
          let uu____76830 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76830, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76824  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76823  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76844 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76844  in
    let uu____76849 =
      let uu____76850 =
        let uu____76858 =
          let uu____76859 = FStar_TypeChecker_Env.get_range env  in
          let uu____76860 =
            let uu____76871 =
              let uu____76876 =
                let uu____76879 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76879]  in
              [uu____76876]  in
            let uu____76884 =
              let uu____76885 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76885 tt  in
            (uu____76871, [bb], uu____76884)  in
          FStar_SMTEncoding_Term.mkForall uu____76859 uu____76860  in
        (uu____76858, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76850  in
    let uu____76910 =
      let uu____76913 =
        let uu____76914 =
          let uu____76922 =
            let uu____76923 =
              let uu____76934 =
                let uu____76935 =
                  let uu____76940 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76940)  in
                FStar_SMTEncoding_Util.mkImp uu____76935  in
              ([[typing_pred]], [xx], uu____76934)  in
            let uu____76967 =
              let uu____76982 = FStar_TypeChecker_Env.get_range env  in
              let uu____76983 = mkForall_fuel1 env  in
              uu____76983 uu____76982  in
            uu____76967 uu____76923  in
          (uu____76922, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76914  in
      let uu____77005 =
        let uu____77008 =
          let uu____77009 =
            let uu____77017 =
              let uu____77018 =
                let uu____77029 =
                  let uu____77030 =
                    let uu____77035 =
                      let uu____77036 =
                        let uu____77039 =
                          let uu____77042 =
                            let uu____77045 =
                              let uu____77046 =
                                let uu____77051 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____77052 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____77051, uu____77052)  in
                              FStar_SMTEncoding_Util.mkGT uu____77046  in
                            let uu____77054 =
                              let uu____77057 =
                                let uu____77058 =
                                  let uu____77063 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____77064 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____77063, uu____77064)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77058  in
                              let uu____77066 =
                                let uu____77069 =
                                  let uu____77070 =
                                    let uu____77075 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____77076 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____77075, uu____77076)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77070  in
                                [uu____77069]  in
                              uu____77057 :: uu____77066  in
                            uu____77045 :: uu____77054  in
                          typing_pred_y :: uu____77042  in
                        typing_pred :: uu____77039  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77036  in
                    (uu____77035, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77030  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77029)
                 in
              let uu____77109 =
                let uu____77124 = FStar_TypeChecker_Env.get_range env  in
                let uu____77125 = mkForall_fuel1 env  in
                uu____77125 uu____77124  in
              uu____77109 uu____77018  in
            (uu____77017,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77009  in
        [uu____77008]  in
      uu____76913 :: uu____77005  in
    uu____76849 :: uu____76910  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77168 =
        let uu____77169 =
          let uu____77175 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77175, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77169  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77168  in
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
      let uu____77191 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77191  in
    let uu____77196 =
      let uu____77197 =
        let uu____77205 =
          let uu____77206 = FStar_TypeChecker_Env.get_range env  in
          let uu____77207 =
            let uu____77218 =
              let uu____77223 =
                let uu____77226 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77226]  in
              [uu____77223]  in
            let uu____77231 =
              let uu____77232 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77232 tt  in
            (uu____77218, [bb], uu____77231)  in
          FStar_SMTEncoding_Term.mkForall uu____77206 uu____77207  in
        (uu____77205, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77197  in
    let uu____77257 =
      let uu____77260 =
        let uu____77261 =
          let uu____77269 =
            let uu____77270 =
              let uu____77281 =
                let uu____77282 =
                  let uu____77287 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77287)  in
                FStar_SMTEncoding_Util.mkImp uu____77282  in
              ([[typing_pred]], [xx], uu____77281)  in
            let uu____77314 =
              let uu____77329 = FStar_TypeChecker_Env.get_range env  in
              let uu____77330 = mkForall_fuel1 env  in
              uu____77330 uu____77329  in
            uu____77314 uu____77270  in
          (uu____77269, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77261  in
      let uu____77352 =
        let uu____77355 =
          let uu____77356 =
            let uu____77364 =
              let uu____77365 =
                let uu____77376 =
                  let uu____77377 =
                    let uu____77382 =
                      let uu____77383 =
                        let uu____77386 =
                          let uu____77389 =
                            let uu____77392 =
                              let uu____77393 =
                                let uu____77398 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77399 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77398, uu____77399)  in
                              FStar_SMTEncoding_Util.mkGT uu____77393  in
                            let uu____77401 =
                              let uu____77404 =
                                let uu____77405 =
                                  let uu____77410 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77411 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77410, uu____77411)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77405  in
                              let uu____77413 =
                                let uu____77416 =
                                  let uu____77417 =
                                    let uu____77422 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77423 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77422, uu____77423)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77417  in
                                [uu____77416]  in
                              uu____77404 :: uu____77413  in
                            uu____77392 :: uu____77401  in
                          typing_pred_y :: uu____77389  in
                        typing_pred :: uu____77386  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77383  in
                    (uu____77382, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77377  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77376)
                 in
              let uu____77456 =
                let uu____77471 = FStar_TypeChecker_Env.get_range env  in
                let uu____77472 = mkForall_fuel1 env  in
                uu____77472 uu____77471  in
              uu____77456 uu____77365  in
            (uu____77364,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77356  in
        [uu____77355]  in
      uu____77260 :: uu____77352  in
    uu____77196 :: uu____77257  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77519 =
      let uu____77520 =
        let uu____77528 =
          let uu____77529 = FStar_TypeChecker_Env.get_range env  in
          let uu____77530 =
            let uu____77541 =
              let uu____77546 =
                let uu____77549 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77549]  in
              [uu____77546]  in
            let uu____77554 =
              let uu____77555 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77555 tt  in
            (uu____77541, [bb], uu____77554)  in
          FStar_SMTEncoding_Term.mkForall uu____77529 uu____77530  in
        (uu____77528, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77520  in
    let uu____77580 =
      let uu____77583 =
        let uu____77584 =
          let uu____77592 =
            let uu____77593 =
              let uu____77604 =
                let uu____77605 =
                  let uu____77610 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77610)  in
                FStar_SMTEncoding_Util.mkImp uu____77605  in
              ([[typing_pred]], [xx], uu____77604)  in
            let uu____77637 =
              let uu____77652 = FStar_TypeChecker_Env.get_range env  in
              let uu____77653 = mkForall_fuel1 env  in
              uu____77653 uu____77652  in
            uu____77637 uu____77593  in
          (uu____77592, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77584  in
      [uu____77583]  in
    uu____77519 :: uu____77580  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77700 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77700]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77730 =
      let uu____77731 =
        let uu____77739 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77739, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77731  in
    [uu____77730]  in
  let mk_and_interp env conj uu____77762 =
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
    let uu____77791 =
      let uu____77792 =
        let uu____77800 =
          let uu____77801 = FStar_TypeChecker_Env.get_range env  in
          let uu____77802 =
            let uu____77813 =
              let uu____77814 =
                let uu____77819 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77819, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77814  in
            ([[l_and_a_b]], [aa; bb], uu____77813)  in
          FStar_SMTEncoding_Term.mkForall uu____77801 uu____77802  in
        (uu____77800, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77792  in
    [uu____77791]  in
  let mk_or_interp env disj uu____77874 =
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
    let uu____77903 =
      let uu____77904 =
        let uu____77912 =
          let uu____77913 = FStar_TypeChecker_Env.get_range env  in
          let uu____77914 =
            let uu____77925 =
              let uu____77926 =
                let uu____77931 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77931, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77926  in
            ([[l_or_a_b]], [aa; bb], uu____77925)  in
          FStar_SMTEncoding_Term.mkForall uu____77913 uu____77914  in
        (uu____77912, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77904  in
    [uu____77903]  in
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
    let uu____78009 =
      let uu____78010 =
        let uu____78018 =
          let uu____78019 = FStar_TypeChecker_Env.get_range env  in
          let uu____78020 =
            let uu____78031 =
              let uu____78032 =
                let uu____78037 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78037, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78032  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____78031)  in
          FStar_SMTEncoding_Term.mkForall uu____78019 uu____78020  in
        (uu____78018, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78010  in
    [uu____78009]  in
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
    let uu____78127 =
      let uu____78128 =
        let uu____78136 =
          let uu____78137 = FStar_TypeChecker_Env.get_range env  in
          let uu____78138 =
            let uu____78149 =
              let uu____78150 =
                let uu____78155 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78155, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78150  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78149)  in
          FStar_SMTEncoding_Term.mkForall uu____78137 uu____78138  in
        (uu____78136, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78128  in
    [uu____78127]  in
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
    let uu____78255 =
      let uu____78256 =
        let uu____78264 =
          let uu____78265 = FStar_TypeChecker_Env.get_range env  in
          let uu____78266 =
            let uu____78277 =
              let uu____78278 =
                let uu____78283 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78283, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78278  in
            ([[l_imp_a_b]], [aa; bb], uu____78277)  in
          FStar_SMTEncoding_Term.mkForall uu____78265 uu____78266  in
        (uu____78264, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78256  in
    [uu____78255]  in
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
    let uu____78367 =
      let uu____78368 =
        let uu____78376 =
          let uu____78377 = FStar_TypeChecker_Env.get_range env  in
          let uu____78378 =
            let uu____78389 =
              let uu____78390 =
                let uu____78395 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78395, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78390  in
            ([[l_iff_a_b]], [aa; bb], uu____78389)  in
          FStar_SMTEncoding_Term.mkForall uu____78377 uu____78378  in
        (uu____78376, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78368  in
    [uu____78367]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78466 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78466  in
    let uu____78471 =
      let uu____78472 =
        let uu____78480 =
          let uu____78481 = FStar_TypeChecker_Env.get_range env  in
          let uu____78482 =
            let uu____78493 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78493)  in
          FStar_SMTEncoding_Term.mkForall uu____78481 uu____78482  in
        (uu____78480, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78472  in
    [uu____78471]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78546 =
      let uu____78547 =
        let uu____78555 =
          let uu____78556 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78556 range_ty  in
        let uu____78557 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78555, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78557)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78547  in
    [uu____78546]  in
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
        let uu____78603 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78603 x1 t  in
      let uu____78605 = FStar_TypeChecker_Env.get_range env  in
      let uu____78606 =
        let uu____78617 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78617)  in
      FStar_SMTEncoding_Term.mkForall uu____78605 uu____78606  in
    let uu____78642 =
      let uu____78643 =
        let uu____78651 =
          let uu____78652 = FStar_TypeChecker_Env.get_range env  in
          let uu____78653 =
            let uu____78664 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78664)  in
          FStar_SMTEncoding_Term.mkForall uu____78652 uu____78653  in
        (uu____78651,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78643  in
    [uu____78642]  in
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
    let uu____78725 =
      let uu____78726 =
        let uu____78734 =
          let uu____78735 = FStar_TypeChecker_Env.get_range env  in
          let uu____78736 =
            let uu____78752 =
              let uu____78753 =
                let uu____78758 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78759 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78758, uu____78759)  in
              FStar_SMTEncoding_Util.mkAnd uu____78753  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78752)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78735 uu____78736  in
        (uu____78734,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78726  in
    [uu____78725]  in
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
          let uu____79317 =
            FStar_Util.find_opt
              (fun uu____79355  ->
                 match uu____79355 with
                 | (l,uu____79371) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79317 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79414,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79475 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79475 with
        | (form,decls) ->
            let uu____79484 =
              let uu____79487 =
                let uu____79490 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79490]  in
              FStar_All.pipe_right uu____79487
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79484
  
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
              let uu____79549 =
                ((let uu____79553 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79553) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79549
              then
                let arg_sorts =
                  let uu____79565 =
                    let uu____79566 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79566.FStar_Syntax_Syntax.n  in
                  match uu____79565 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79572) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79610  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79617 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79619 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79619 with
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
                    let uu____79655 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79655, env1)
              else
                (let uu____79660 = prims.is lid  in
                 if uu____79660
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79669 = prims.mk lid vname  in
                   match uu____79669 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79693 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79693, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79702 =
                      let uu____79721 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79721 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79749 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79749
                            then
                              let uu____79754 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79757 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79757.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79757.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79757.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79757.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79757.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79757.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79757.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79757.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79757.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79757.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79757.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79757.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79757.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79757.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79757.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79757.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79757.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79757.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79757.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79757.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79757.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79757.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79757.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79757.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79757.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79757.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79757.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79757.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79757.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79757.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79757.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79757.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79757.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79757.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79757.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79757.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79757.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79757.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79757.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79757.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79757.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79757.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79754
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79780 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79780)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79702 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79886  ->
                                  match uu___639_79886 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79890 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79890 with
                                       | (uu____79923,xxv) ->
                                           let xx =
                                             let uu____79962 =
                                               let uu____79963 =
                                                 let uu____79969 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79969,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79963
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79962
                                              in
                                           let uu____79972 =
                                             let uu____79973 =
                                               let uu____79981 =
                                                 let uu____79982 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79983 =
                                                   let uu____79994 =
                                                     let uu____79995 =
                                                       let uu____80000 =
                                                         let uu____80001 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____80001
                                                          in
                                                       (vapp, uu____80000)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79995
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79994)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79982 uu____79983
                                                  in
                                               (uu____79981,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79973
                                              in
                                           [uu____79972])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____80016 =
                                        FStar_Util.prefix vars  in
                                      (match uu____80016 with
                                       | (uu____80049,xxv) ->
                                           let xx =
                                             let uu____80088 =
                                               let uu____80089 =
                                                 let uu____80095 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____80095,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____80089
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____80088
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
                                           let uu____80106 =
                                             let uu____80107 =
                                               let uu____80115 =
                                                 let uu____80116 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80117 =
                                                   let uu____80128 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80128)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80116 uu____80117
                                                  in
                                               (uu____80115,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80107
                                              in
                                           [uu____80106])
                                  | uu____80141 -> []))
                           in
                        let uu____80142 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80142 with
                         | (vars,guards,env',decls1,uu____80167) ->
                             let uu____80180 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80193 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80193, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80197 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80197 with
                                    | (g,ds) ->
                                        let uu____80210 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80210,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80180 with
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
                                  let should_thunk uu____80233 =
                                    let is_type1 t =
                                      let uu____80241 =
                                        let uu____80242 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80242.FStar_Syntax_Syntax.n  in
                                      match uu____80241 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80246 -> true
                                      | uu____80248 -> false  in
                                    let is_squash1 t =
                                      let uu____80257 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80257 with
                                      | (head1,uu____80276) ->
                                          let uu____80301 =
                                            let uu____80302 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80302.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80301 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80307;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80308;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80310;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80311;_};_},uu____80312)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80320 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80325 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80325))
                                       &&
                                       (let uu____80331 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80331))
                                      &&
                                      (let uu____80334 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80334)
                                     in
                                  let uu____80336 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80395 -> (false, vars)  in
                                  (match uu____80336 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80445 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80445 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80481 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80490 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80490
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80501 ->
                                                  let uu____80510 =
                                                    let uu____80518 =
                                                      get_vtok ()  in
                                                    (uu____80518, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80510
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80525 =
                                                let uu____80533 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80533)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80525
                                               in
                                            let uu____80547 =
                                              let vname_decl =
                                                let uu____80555 =
                                                  let uu____80567 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80567,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80555
                                                 in
                                              let uu____80578 =
                                                let env2 =
                                                  let uu___1026_80584 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80584.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80585 =
                                                  let uu____80587 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80587
                                                   in
                                                if uu____80585
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80578 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80604 =
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
                                                        let uu____80630 =
                                                          let uu____80633 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80633
                                                           in
                                                        let uu____80640 =
                                                          let uu____80641 =
                                                            let uu____80644 =
                                                              let uu____80645
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80645
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80649  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80649)
                                                              uu____80644
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80641
                                                           in
                                                        (uu____80630,
                                                          uu____80640)
                                                    | uu____80656 when
                                                        thunked ->
                                                        let uu____80667 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80667
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80682
                                                                 =
                                                                 let uu____80690
                                                                   =
                                                                   let uu____80693
                                                                    =
                                                                    let uu____80696
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80696]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80693
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80690)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80682
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80704
                                                               =
                                                               let uu____80712
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80712,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80704
                                                              in
                                                           let uu____80717 =
                                                             let uu____80720
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80720
                                                              in
                                                           (uu____80717,
                                                             env1))
                                                    | uu____80729 ->
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
                                                          let uu____80753 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80754 =
                                                            let uu____80765 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80765)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80753
                                                            uu____80754
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80775 =
                                                            let uu____80783 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80783,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80775
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
                                                            let uu____80794 =
                                                              let uu____80795
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80795]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80794
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80822 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80823 =
                                                              let uu____80834
                                                                =
                                                                let uu____80835
                                                                  =
                                                                  let uu____80840
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80841
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80840,
                                                                    uu____80841)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80835
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80834)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80822
                                                              uu____80823
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80870 =
                                                          let uu____80873 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80873
                                                           in
                                                        (uu____80870, env1)
                                                     in
                                                  (match uu____80604 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80894 =
                                                         let uu____80897 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80897
                                                           tok_decl
                                                          in
                                                       (uu____80894, env2))
                                               in
                                            (match uu____80547 with
                                             | (decls2,env2) ->
                                                 let uu____80916 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80926 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80926 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80941 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80941, decls)
                                                    in
                                                 (match uu____80916 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80956 =
                                                          let uu____80964 =
                                                            let uu____80965 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80966 =
                                                              let uu____80977
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80977)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80965
                                                              uu____80966
                                                             in
                                                          (uu____80964,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80956
                                                         in
                                                      let freshness =
                                                        let uu____80993 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80993
                                                        then
                                                          let uu____81001 =
                                                            let uu____81002 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____81003 =
                                                              let uu____81016
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____81023
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____81016,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____81023)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____81002
                                                              uu____81003
                                                             in
                                                          let uu____81029 =
                                                            let uu____81032 =
                                                              let uu____81033
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____81033
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____81032]  in
                                                          uu____81001 ::
                                                            uu____81029
                                                        else []  in
                                                      let g =
                                                        let uu____81039 =
                                                          let uu____81042 =
                                                            let uu____81045 =
                                                              let uu____81048
                                                                =
                                                                let uu____81051
                                                                  =
                                                                  let uu____81054
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____81054
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____81051
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____81048
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____81045
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____81042
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____81039
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
          let uu____81094 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____81094 with
          | FStar_Pervasives_Native.None  ->
              let uu____81105 = encode_free_var false env x t t_norm []  in
              (match uu____81105 with
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
            let uu____81168 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81168 with
            | (decls,env1) ->
                let uu____81179 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81179
                then
                  let uu____81186 =
                    let uu____81187 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81187  in
                  (uu____81186, env1)
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
             (fun uu____81243  ->
                fun lb  ->
                  match uu____81243 with
                  | (decls,env1) ->
                      let uu____81263 =
                        let uu____81268 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81268
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81263 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81297 = FStar_Syntax_Util.head_and_args t  in
    match uu____81297 with
    | (hd1,args) ->
        let uu____81341 =
          let uu____81342 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81342.FStar_Syntax_Syntax.n  in
        (match uu____81341 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81348,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81372 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81383 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81391 = en  in
    let uu____81392 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81391.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81391.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81391.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81391.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81391.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81391.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81391.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81391.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81391.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81391.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81392
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81422  ->
      fun quals  ->
        match uu____81422 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81527 = FStar_Util.first_N nbinders formals  in
              match uu____81527 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81628  ->
                         fun uu____81629  ->
                           match (uu____81628, uu____81629) with
                           | ((formal,uu____81655),(binder,uu____81657)) ->
                               let uu____81678 =
                                 let uu____81685 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81685)  in
                               FStar_Syntax_Syntax.NT uu____81678) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81699 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81740  ->
                              match uu____81740 with
                              | (x,i) ->
                                  let uu____81759 =
                                    let uu___1139_81760 = x  in
                                    let uu____81761 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81760.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81760.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81761
                                    }  in
                                  (uu____81759, i)))
                       in
                    FStar_All.pipe_right uu____81699
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81785 =
                      let uu____81790 = FStar_Syntax_Subst.compress body  in
                      let uu____81791 =
                        let uu____81792 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81792
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81790
                        uu____81791
                       in
                    uu____81785 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81843 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81843.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81843.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81843.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81843.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81843.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81843.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81843.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81843.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81843.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81843.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81843.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81843.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81843.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81843.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81843.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81843.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81843.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81843.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81843.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81843.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81843.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81843.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81843.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81843.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81843.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81843.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81843.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81843.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81843.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81843.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81843.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81843.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81843.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81843.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81843.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81843.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81843.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81843.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81843.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81843.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81843.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81843.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81915  ->
                       fun uu____81916  ->
                         match (uu____81915, uu____81916) with
                         | ((x,uu____81942),(b,uu____81944)) ->
                             let uu____81965 =
                               let uu____81972 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81972)  in
                             FStar_Syntax_Syntax.NT uu____81965) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81997 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81997
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____82026 ->
                    let uu____82033 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____82033
                | uu____82034 when Prims.op_Negation norm1 ->
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
                | uu____82037 ->
                    let uu____82038 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____82038)
                 in
              let aux t1 e1 =
                let uu____82080 = FStar_Syntax_Util.abs_formals e1  in
                match uu____82080 with
                | (binders,body,lopt) ->
                    let uu____82112 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82128 -> arrow_formals_comp_norm false t1  in
                    (match uu____82112 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82162 =
                           if nformals < nbinders
                           then
                             let uu____82206 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82206 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82290 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82290)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82330 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82330 with
                                | (binders1,body1) ->
                                    let uu____82383 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82383))
                             else
                               (let uu____82396 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82396))
                            in
                         (match uu____82162 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82456 = aux t e  in
              match uu____82456 with
              | (binders,body,comp) ->
                  let uu____82502 =
                    let uu____82513 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82513
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82528 = aux comp1 body1  in
                      match uu____82528 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82502 with
                   | (binders1,body1,comp1) ->
                       let uu____82611 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82611, comp1))
               in
            (try
               (fun uu___1216_82638  ->
                  match () with
                  | () ->
                      let uu____82645 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82645
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82661 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82724  ->
                                   fun lb  ->
                                     match uu____82724 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82779 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82779
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82785 =
                                             let uu____82794 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82794
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82785 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82661 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82935;
                                    FStar_Syntax_Syntax.lbeff = uu____82936;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82938;
                                    FStar_Syntax_Syntax.lbpos = uu____82939;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82963 =
                                     let uu____82970 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82970 with
                                     | (tcenv',uu____82986,e_t) ->
                                         let uu____82992 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____83003 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82992 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_83020 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_83020.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82963 with
                                    | (env',e1,t_norm1) ->
                                        let uu____83030 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____83030 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____83050 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____83050
                                               then
                                                 let uu____83055 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____83058 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____83055 uu____83058
                                               else ());
                                              (let uu____83063 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____83063 with
                                               | (vars,_guards,env'1,binder_decls,uu____83090)
                                                   ->
                                                   let uu____83103 =
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
                                                         let uu____83120 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83120
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83142 =
                                                          let uu____83143 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83144 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83143 fvb
                                                            uu____83144
                                                           in
                                                        (vars, uu____83142))
                                                      in
                                                   (match uu____83103 with
                                                    | (vars1,app) ->
                                                        let uu____83155 =
                                                          let is_logical =
                                                            let uu____83168 =
                                                              let uu____83169
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83169.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83168
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83175 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83179 =
                                                              let uu____83180
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83180
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83179
                                                              (fun lid  ->
                                                                 let uu____83189
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83189
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83190 =
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
                                                          if uu____83190
                                                          then
                                                            let uu____83206 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83207 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83206,
                                                              uu____83207)
                                                          else
                                                            (let uu____83218
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83218))
                                                           in
                                                        (match uu____83155
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
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
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83263)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83251
                                                                    uu____83252
                                                                    in
                                                                 let uu____83272
                                                                   =
                                                                   let uu____83273
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83273
                                                                    in
                                                                 (uu____83250,
                                                                   uu____83272,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83242
                                                                in
                                                             let uu____83279
                                                               =
                                                               let uu____83282
                                                                 =
                                                                 let uu____83285
                                                                   =
                                                                   let uu____83288
                                                                    =
                                                                    let uu____83291
                                                                    =
                                                                    let uu____83294
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83294
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83291
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83288
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83285
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83282
                                                                in
                                                             (uu____83279,
                                                               env2)))))))
                               | uu____83303 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83363 =
                                   let uu____83369 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83369,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83363  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83375 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83428  ->
                                         fun fvb  ->
                                           match uu____83428 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83483 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83483
                                                  in
                                               let gtok =
                                                 let uu____83487 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83487
                                                  in
                                               let env4 =
                                                 let uu____83490 =
                                                   let uu____83493 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83499  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83499) uu____83493
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83490
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83375 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83619
                                     t_norm uu____83621 =
                                     match (uu____83619, uu____83621) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83651;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83652;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83654;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83655;_})
                                         ->
                                         let uu____83682 =
                                           let uu____83689 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83689 with
                                           | (tcenv',uu____83705,e_t) ->
                                               let uu____83711 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83722 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83711 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83739 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83739.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83682 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83752 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83752
                                                then
                                                  let uu____83757 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83759 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83761 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83757 uu____83759
                                                    uu____83761
                                                else ());
                                               (let uu____83766 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83766 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83793 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83793 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83815 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83815
                                                           then
                                                             let uu____83820
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83822
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83825
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83827
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83820
                                                               uu____83822
                                                               uu____83825
                                                               uu____83827
                                                           else ());
                                                          (let uu____83832 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83832
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83861)
                                                               ->
                                                               let uu____83874
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83887
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83887,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83891
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83891
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83904
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83904,
                                                                    decls0))
                                                                  in
                                                               (match uu____83874
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
                                                                    let uu____83925
                                                                    =
                                                                    let uu____83937
                                                                    =
                                                                    let uu____83940
                                                                    =
                                                                    let uu____83943
                                                                    =
                                                                    let uu____83946
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83946
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83943
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83940
                                                                     in
                                                                    (g,
                                                                    uu____83937,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83925
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
                                                                    let uu____83976
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83976
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
                                                                    let uu____83991
                                                                    =
                                                                    let uu____83994
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83994
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83991
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____84000
                                                                    =
                                                                    let uu____84003
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____84003
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84000
                                                                     in
                                                                    let uu____84008
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____84008
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____84024
                                                                    =
                                                                    let uu____84032
                                                                    =
                                                                    let uu____84033
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84034
                                                                    =
                                                                    let uu____84050
                                                                    =
                                                                    let uu____84051
                                                                    =
                                                                    let uu____84056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____84056)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84051
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84050)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____84033
                                                                    uu____84034
                                                                     in
                                                                    let uu____84070
                                                                    =
                                                                    let uu____84071
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84071
                                                                     in
                                                                    (uu____84032,
                                                                    uu____84070,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84024
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____84078
                                                                    =
                                                                    let uu____84086
                                                                    =
                                                                    let uu____84087
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84088
                                                                    =
                                                                    let uu____84099
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84099)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84087
                                                                    uu____84088
                                                                     in
                                                                    (uu____84086,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84078
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84113
                                                                    =
                                                                    let uu____84121
                                                                    =
                                                                    let uu____84122
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84123
                                                                    =
                                                                    let uu____84134
                                                                    =
                                                                    let uu____84135
                                                                    =
                                                                    let uu____84140
                                                                    =
                                                                    let uu____84141
                                                                    =
                                                                    let uu____84144
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84144
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84141
                                                                     in
                                                                    (gsapp,
                                                                    uu____84140)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84135
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84134)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84122
                                                                    uu____84123
                                                                     in
                                                                    (uu____84121,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84113
                                                                     in
                                                                    let uu____84158
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
                                                                    let uu____84170
                                                                    =
                                                                    let uu____84171
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84171
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84170
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84173
                                                                    =
                                                                    let uu____84181
                                                                    =
                                                                    let uu____84182
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84183
                                                                    =
                                                                    let uu____84194
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84194)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84182
                                                                    uu____84183
                                                                     in
                                                                    (uu____84181,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84173
                                                                     in
                                                                    let uu____84207
                                                                    =
                                                                    let uu____84216
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84216
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84231
                                                                    =
                                                                    let uu____84234
                                                                    =
                                                                    let uu____84235
                                                                    =
                                                                    let uu____84243
                                                                    =
                                                                    let uu____84244
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84245
                                                                    =
                                                                    let uu____84256
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84256)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84244
                                                                    uu____84245
                                                                     in
                                                                    (uu____84243,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84235
                                                                     in
                                                                    [uu____84234]
                                                                     in
                                                                    (d3,
                                                                    uu____84231)
                                                                     in
                                                                    match uu____84207
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84158
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84313
                                                                    =
                                                                    let uu____84316
                                                                    =
                                                                    let uu____84319
                                                                    =
                                                                    let uu____84322
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84322
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84319
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84316
                                                                     in
                                                                    let uu____84329
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84313,
                                                                    uu____84329,
                                                                    env02))))))))))
                                      in
                                   let uu____84334 =
                                     let uu____84347 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84410  ->
                                          fun uu____84411  ->
                                            match (uu____84410, uu____84411)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84536 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84536 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84347
                                      in
                                   (match uu____84334 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84603 =
                                          let isDeclFun uu___640_84620 =
                                            match uu___640_84620 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84622 -> true
                                            | uu____84635 -> false  in
                                          let uu____84637 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84637
                                            (fun decls3  ->
                                               let uu____84667 =
                                                 FStar_List.fold_left
                                                   (fun uu____84698  ->
                                                      fun elt  ->
                                                        match uu____84698
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84739 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84739
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84767
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84767
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
                                                                    let uu___1459_84805
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84805.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84805.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84805.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84667 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84837 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84837, elts, rest))
                                           in
                                        (match uu____84603 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84866 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84872  ->
                                        match uu___641_84872 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84875 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84883 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84883)))
                                in
                             if uu____84866
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84905  ->
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
                   let uu____84944 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84944
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84963 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84963, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____85019 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____85019 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____85025 = encode_sigelt' env se  in
      match uu____85025 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____85037 =
                  let uu____85040 =
                    let uu____85041 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____85041  in
                  [uu____85040]  in
                FStar_All.pipe_right uu____85037
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____85046 ->
                let uu____85047 =
                  let uu____85050 =
                    let uu____85053 =
                      let uu____85054 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____85054  in
                    [uu____85053]  in
                  FStar_All.pipe_right uu____85050
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____85061 =
                  let uu____85064 =
                    let uu____85067 =
                      let uu____85070 =
                        let uu____85071 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____85071  in
                      [uu____85070]  in
                    FStar_All.pipe_right uu____85067
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____85064  in
                FStar_List.append uu____85047 uu____85061
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____85085 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____85085
       then
         let uu____85090 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____85090
       else ());
      (let is_opaque_to_smt t =
         let uu____85102 =
           let uu____85103 = FStar_Syntax_Subst.compress t  in
           uu____85103.FStar_Syntax_Syntax.n  in
         match uu____85102 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85108)) -> s = "opaque_to_smt"
         | uu____85113 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85122 =
           let uu____85123 = FStar_Syntax_Subst.compress t  in
           uu____85123.FStar_Syntax_Syntax.n  in
         match uu____85122 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85128)) -> s = "uninterpreted_by_smt"
         | uu____85133 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85139 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85145 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85157 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85158 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85159 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85172 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85174 =
             let uu____85176 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85176  in
           if uu____85174
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85205 ->
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
                let uu____85237 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85237 with
                | (formals,uu____85257) ->
                    let arity = FStar_List.length formals  in
                    let uu____85281 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85281 with
                     | (aname,atok,env2) ->
                         let uu____85307 =
                           let uu____85312 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85312 env2
                            in
                         (match uu____85307 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85324 =
                                  let uu____85325 =
                                    let uu____85337 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85357  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85337,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85325
                                   in
                                [uu____85324;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85374 =
                                let aux uu____85420 uu____85421 =
                                  match (uu____85420, uu____85421) with
                                  | ((bv,uu____85465),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85497 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85497 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85520 =
                                             let uu____85523 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85523 :: acc_sorts  in
                                           (env4, uu____85520, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85374 with
                               | (uu____85555,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85571 =
                                       let uu____85579 =
                                         let uu____85580 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85581 =
                                           let uu____85592 =
                                             let uu____85593 =
                                               let uu____85598 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85598)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85593
                                              in
                                           ([[app]], xs_sorts, uu____85592)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85580 uu____85581
                                          in
                                       (uu____85579,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85571
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85613 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85613
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85616 =
                                       let uu____85624 =
                                         let uu____85625 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85626 =
                                           let uu____85637 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85637)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85625 uu____85626
                                          in
                                       (uu____85624,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85616
                                      in
                                   let uu____85650 =
                                     let uu____85653 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85653  in
                                   (env2, uu____85650))))
                 in
              let uu____85662 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85662 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85688,uu____85689)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85690 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85690 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85712,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85719 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85725  ->
                       match uu___642_85725 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85728 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85734 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85737 -> false))
                in
             Prims.op_Negation uu____85719  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85747 =
                let uu____85752 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85752 env fv t quals  in
              match uu____85747 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85766 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85766  in
                  let uu____85769 =
                    let uu____85770 =
                      let uu____85773 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85773
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85770  in
                  (uu____85769, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85783 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85783 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85795 = env  in
                  let uu____85796 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85795.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85795.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85795.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85796;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85795.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85795.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85795.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85795.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85795.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85795.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85795.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85798 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85798 with
                 | (f3,decls) ->
                     let g =
                       let uu____85812 =
                         let uu____85815 =
                           let uu____85816 =
                             let uu____85824 =
                               let uu____85825 =
                                 let uu____85827 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85827
                                  in
                               FStar_Pervasives_Native.Some uu____85825  in
                             let uu____85831 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85824, uu____85831)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85816  in
                         [uu____85815]  in
                       FStar_All.pipe_right uu____85812
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85840) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85854 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85876 =
                        let uu____85879 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85879.FStar_Syntax_Syntax.fv_name  in
                      uu____85876.FStar_Syntax_Syntax.v  in
                    let uu____85880 =
                      let uu____85882 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85882  in
                    if uu____85880
                    then
                      let val_decl =
                        let uu___1629_85914 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85914.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85914.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85914.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85915 = encode_sigelt' env1 val_decl  in
                      match uu____85915 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85854 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85951,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85953;
                           FStar_Syntax_Syntax.lbtyp = uu____85954;
                           FStar_Syntax_Syntax.lbeff = uu____85955;
                           FStar_Syntax_Syntax.lbdef = uu____85956;
                           FStar_Syntax_Syntax.lbattrs = uu____85957;
                           FStar_Syntax_Syntax.lbpos = uu____85958;_}::[]),uu____85959)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85978 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85978 with
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
                  let uu____86016 =
                    let uu____86019 =
                      let uu____86020 =
                        let uu____86028 =
                          let uu____86029 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____86030 =
                            let uu____86041 =
                              let uu____86042 =
                                let uu____86047 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____86047)  in
                              FStar_SMTEncoding_Util.mkEq uu____86042  in
                            ([[b2t_x]], [xx], uu____86041)  in
                          FStar_SMTEncoding_Term.mkForall uu____86029
                            uu____86030
                           in
                        (uu____86028,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____86020  in
                    [uu____86019]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____86016
                   in
                let uu____86085 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____86085, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____86088,uu____86089) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86099  ->
                   match uu___643_86099 with
                   | FStar_Syntax_Syntax.Discriminator uu____86101 -> true
                   | uu____86103 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86105,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86117 =
                      let uu____86119 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86119.FStar_Ident.idText  in
                    uu____86117 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86126  ->
                      match uu___644_86126 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86129 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86132) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86146  ->
                   match uu___645_86146 with
                   | FStar_Syntax_Syntax.Projector uu____86148 -> true
                   | uu____86154 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86158 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86158 with
            | FStar_Pervasives_Native.Some uu____86165 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86167 = se  in
                  let uu____86168 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86168;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86167.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86167.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86167.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86171) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86186) ->
           let uu____86195 = encode_sigelts env ses  in
           (match uu____86195 with
            | (g,env1) ->
                let uu____86206 =
                  FStar_List.fold_left
                    (fun uu____86230  ->
                       fun elt  ->
                         match uu____86230 with
                         | (g',inversions) ->
                             let uu____86258 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86281  ->
                                       match uu___646_86281 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86283;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86284;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86285;_}
                                           -> false
                                       | uu____86292 -> true))
                                in
                             (match uu____86258 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86317 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86317.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86317.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86317.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86206 with
                 | (g',inversions) ->
                     let uu____86336 =
                       FStar_List.fold_left
                         (fun uu____86367  ->
                            fun elt  ->
                              match uu____86367 with
                              | (decls,elts,rest) ->
                                  let uu____86408 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86417  ->
                                            match uu___647_86417 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86419 -> true
                                            | uu____86432 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86408
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86455 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86476  ->
                                               match uu___648_86476 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86478 -> true
                                               | uu____86491 -> false))
                                        in
                                     match uu____86455 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86522 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86522.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86522.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86522.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86336 with
                      | (decls,elts,rest) ->
                          let uu____86548 =
                            let uu____86549 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86556 =
                              let uu____86559 =
                                let uu____86562 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86562  in
                              FStar_List.append elts uu____86559  in
                            FStar_List.append uu____86549 uu____86556  in
                          (uu____86548, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86573,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86586 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86586 with
             | (usubst,uvs) ->
                 let uu____86606 =
                   let uu____86613 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86614 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86615 =
                     let uu____86616 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86616 k  in
                   (uu____86613, uu____86614, uu____86615)  in
                 (match uu____86606 with
                  | (env1,tps1,k1) ->
                      let uu____86629 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86629 with
                       | (tps2,k2) ->
                           let uu____86637 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86637 with
                            | (uu____86653,k3) ->
                                let uu____86675 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86675 with
                                 | (tps3,env_tps,uu____86687,us) ->
                                     let u_k =
                                       let uu____86690 =
                                         let uu____86691 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86692 =
                                           let uu____86697 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86699 =
                                             let uu____86700 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86700
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86697 uu____86699
                                            in
                                         uu____86692
                                           FStar_Pervasives_Native.None
                                           uu____86691
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86690 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86720) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86726,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86729) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86737,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86744) ->
                                           let uu____86745 =
                                             let uu____86747 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86747
                                              in
                                           failwith uu____86745
                                       | (uu____86751,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86752 =
                                             let uu____86754 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86754
                                              in
                                           failwith uu____86752
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86758,uu____86759) ->
                                           let uu____86768 =
                                             let uu____86770 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86770
                                              in
                                           failwith uu____86768
                                       | (uu____86774,FStar_Syntax_Syntax.U_unif
                                          uu____86775) ->
                                           let uu____86784 =
                                             let uu____86786 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86786
                                              in
                                           failwith uu____86784
                                       | uu____86790 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86803 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86803 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86821 = u_leq_u_k u_tp  in
                                       if uu____86821
                                       then true
                                       else
                                         (let uu____86828 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86828 with
                                          | (formals,uu____86845) ->
                                              let uu____86866 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86866 with
                                               | (uu____86876,uu____86877,uu____86878,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86889 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86889
             then
               let uu____86894 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86894
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86914  ->
                       match uu___649_86914 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86918 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86931 = c  in
                 match uu____86931 with
                 | (name,args,uu____86936,uu____86937,uu____86938) ->
                     let uu____86949 =
                       let uu____86950 =
                         let uu____86962 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86989  ->
                                   match uu____86989 with
                                   | (uu____86998,sort,uu____87000) -> sort))
                            in
                         (name, uu____86962,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86950  in
                     [uu____86949]
               else
                 (let uu____87011 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____87011 c)
                in
             let inversion_axioms tapp vars =
               let uu____87029 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____87037 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____87037 FStar_Option.isNone))
                  in
               if uu____87029
               then []
               else
                 (let uu____87072 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____87072 with
                  | (xxsym,xx) ->
                      let uu____87085 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87124  ->
                                fun l  ->
                                  match uu____87124 with
                                  | (out,decls) ->
                                      let uu____87144 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87144 with
                                       | (uu____87155,data_t) ->
                                           let uu____87157 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87157 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87201 =
                                                    let uu____87202 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87202.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87201 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87205,indices)
                                                      -> indices
                                                  | uu____87231 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87261  ->
                                                            match uu____87261
                                                            with
                                                            | (x,uu____87269)
                                                                ->
                                                                let uu____87274
                                                                  =
                                                                  let uu____87275
                                                                    =
                                                                    let uu____87283
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87283,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87275
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87274)
                                                       env)
                                                   in
                                                let uu____87288 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87288 with
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
                                                                  let uu____87323
                                                                    =
                                                                    let uu____87328
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87328,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87323)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87331 =
                                                         let uu____87332 =
                                                           let uu____87337 =
                                                             let uu____87338
                                                               =
                                                               let uu____87343
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87344
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87343,
                                                                 uu____87344)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87338
                                                              in
                                                           (out, uu____87337)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87332
                                                          in
                                                       (uu____87331,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____87085 with
                       | (data_ax,decls) ->
                           let uu____87359 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87359 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87376 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87376 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87383 =
                                    let uu____87391 =
                                      let uu____87392 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87393 =
                                        let uu____87404 =
                                          let uu____87405 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87407 =
                                            let uu____87410 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87410 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87405 uu____87407
                                           in
                                        let uu____87412 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87404,
                                          uu____87412)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87392 uu____87393
                                       in
                                    let uu____87421 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87391,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87421)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87383
                                   in
                                let uu____87427 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87427)))
                in
             let uu____87434 =
               let uu____87439 =
                 let uu____87440 = FStar_Syntax_Subst.compress k  in
                 uu____87440.FStar_Syntax_Syntax.n  in
               match uu____87439 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87475 -> (tps, k)  in
             match uu____87434 with
             | (formals,res) ->
                 let uu____87482 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87482 with
                  | (formals1,res1) ->
                      let uu____87493 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87493 with
                       | (vars,guards,env',binder_decls,uu____87518) ->
                           let arity = FStar_List.length vars  in
                           let uu____87532 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87532 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87562 =
                                    let uu____87570 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87570)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87562
                                   in
                                let uu____87576 =
                                  let tname_decl =
                                    let uu____87586 =
                                      let uu____87587 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87606 =
                                                  let uu____87608 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87608
                                                   in
                                                let uu____87610 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87606, uu____87610,
                                                  false)))
                                         in
                                      let uu____87614 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87587,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87614, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87586
                                     in
                                  let uu____87622 =
                                    match vars with
                                    | [] ->
                                        let uu____87635 =
                                          let uu____87636 =
                                            let uu____87639 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87645  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87645) uu____87639
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87636
                                           in
                                        ([], uu____87635)
                                    | uu____87652 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87662 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87662
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87678 =
                                            let uu____87686 =
                                              let uu____87687 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87688 =
                                                let uu____87704 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87704)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87687 uu____87688
                                               in
                                            (uu____87686,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87678
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87622 with
                                  | (tok_decls,env2) ->
                                      let uu____87731 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87731
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87576 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87759 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87759 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87781 =
                                                 let uu____87782 =
                                                   let uu____87790 =
                                                     let uu____87791 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87791
                                                      in
                                                   (uu____87790,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87782
                                                  in
                                               [uu____87781]
                                             else []  in
                                           let uu____87799 =
                                             let uu____87802 =
                                               let uu____87805 =
                                                 let uu____87808 =
                                                   let uu____87809 =
                                                     let uu____87817 =
                                                       let uu____87818 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87819 =
                                                         let uu____87830 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87830)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87818
                                                         uu____87819
                                                        in
                                                     (uu____87817,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87809
                                                    in
                                                 [uu____87808]  in
                                               FStar_List.append karr
                                                 uu____87805
                                                in
                                             FStar_All.pipe_right uu____87802
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87799
                                        in
                                     let aux =
                                       let uu____87849 =
                                         let uu____87852 =
                                           inversion_axioms tapp vars  in
                                         let uu____87855 =
                                           let uu____87858 =
                                             let uu____87861 =
                                               let uu____87862 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87862 env2
                                                 tapp vars
                                                in
                                             [uu____87861]  in
                                           FStar_All.pipe_right uu____87858
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87852
                                           uu____87855
                                          in
                                       FStar_List.append kindingAx
                                         uu____87849
                                        in
                                     let g =
                                       let uu____87870 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87870
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87878,uu____87879,uu____87880,uu____87881,uu____87882)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87890,t,uu____87892,n_tps,uu____87894) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87904 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87904 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87952 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87952 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87980 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87980 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____88000 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____88000 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____88079 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____88079,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____88086 =
                                   let uu____88087 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____88087, true)
                                    in
                                 let uu____88095 =
                                   let uu____88102 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88102
                                    in
                                 FStar_All.pipe_right uu____88086 uu____88095
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
                               let uu____88114 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88114 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88126::uu____88127 ->
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
                                            let uu____88176 =
                                              let uu____88177 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88177]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88176
                                             in
                                          let uu____88203 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88204 =
                                            let uu____88215 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88215)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88203 uu____88204
                                      | uu____88242 -> tok_typing  in
                                    let uu____88253 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88253 with
                                     | (vars',guards',env'',decls_formals,uu____88278)
                                         ->
                                         let uu____88291 =
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
                                         (match uu____88291 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88321 ->
                                                    let uu____88330 =
                                                      let uu____88331 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88331
                                                       in
                                                    [uu____88330]
                                                 in
                                              let encode_elim uu____88347 =
                                                let uu____88348 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88348 with
                                                | (head1,args) ->
                                                    let uu____88399 =
                                                      let uu____88400 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88400.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88399 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88412;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88413;_},uu____88414)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88420 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88420
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
                                                                  | uu____88483
                                                                    ->
                                                                    let uu____88484
                                                                    =
                                                                    let uu____88490
                                                                    =
                                                                    let uu____88492
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88492
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88490)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88484
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88515
                                                                    =
                                                                    let uu____88517
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88517
                                                                     in
                                                                    if
                                                                    uu____88515
                                                                    then
                                                                    let uu____88539
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88539]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88542
                                                                =
                                                                let uu____88556
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88613
                                                                     ->
                                                                    fun
                                                                    uu____88614
                                                                     ->
                                                                    match 
                                                                    (uu____88613,
                                                                    uu____88614)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88725
                                                                    =
                                                                    let uu____88733
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88733
                                                                     in
                                                                    (match uu____88725
                                                                    with
                                                                    | 
                                                                    (uu____88747,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88758
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88758
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88763
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88763
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
                                                                  uu____88556
                                                                 in
                                                              (match uu____88542
                                                               with
                                                               | (uu____88784,arg_vars,elim_eqns_or_guards,uu____88787)
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
                                                                    let uu____88814
                                                                    =
                                                                    let uu____88822
                                                                    =
                                                                    let uu____88823
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88824
                                                                    =
                                                                    let uu____88835
                                                                    =
                                                                    let uu____88836
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88836
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88838
                                                                    =
                                                                    let uu____88839
                                                                    =
                                                                    let uu____88844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88844)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88839
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88835,
                                                                    uu____88838)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88823
                                                                    uu____88824
                                                                     in
                                                                    (uu____88822,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88814
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88859
                                                                    =
                                                                    let uu____88860
                                                                    =
                                                                    let uu____88866
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88866,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88860
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88859
                                                                     in
                                                                    let uu____88869
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88869
                                                                    then
                                                                    let x =
                                                                    let uu____88873
                                                                    =
                                                                    let uu____88879
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88879,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88873
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88884
                                                                    =
                                                                    let uu____88892
                                                                    =
                                                                    let uu____88893
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88894
                                                                    =
                                                                    let uu____88905
                                                                    =
                                                                    let uu____88910
                                                                    =
                                                                    let uu____88913
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88913]
                                                                     in
                                                                    [uu____88910]
                                                                     in
                                                                    let uu____88918
                                                                    =
                                                                    let uu____88919
                                                                    =
                                                                    let uu____88924
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88924,
                                                                    uu____88926)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88919
                                                                     in
                                                                    (uu____88905,
                                                                    [x],
                                                                    uu____88918)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88893
                                                                    uu____88894
                                                                     in
                                                                    let uu____88947
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88892,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88947)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88884
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88958
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
                                                                    (let uu____88981
                                                                    =
                                                                    let uu____88982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88982
                                                                    dapp1  in
                                                                    [uu____88981])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88958
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88989
                                                                    =
                                                                    let uu____88997
                                                                    =
                                                                    let uu____88998
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88999
                                                                    =
                                                                    let uu____89010
                                                                    =
                                                                    let uu____89011
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89011
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89013
                                                                    =
                                                                    let uu____89014
                                                                    =
                                                                    let uu____89019
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89019)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89014
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89010,
                                                                    uu____89013)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88998
                                                                    uu____88999
                                                                     in
                                                                    (uu____88997,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88989)
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
                                                         let uu____89038 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____89038
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
                                                                  | uu____89101
                                                                    ->
                                                                    let uu____89102
                                                                    =
                                                                    let uu____89108
                                                                    =
                                                                    let uu____89110
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89110
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89108)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89102
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89133
                                                                    =
                                                                    let uu____89135
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89135
                                                                     in
                                                                    if
                                                                    uu____89133
                                                                    then
                                                                    let uu____89157
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89157]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89160
                                                                =
                                                                let uu____89174
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89231
                                                                     ->
                                                                    fun
                                                                    uu____89232
                                                                     ->
                                                                    match 
                                                                    (uu____89231,
                                                                    uu____89232)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89343
                                                                    =
                                                                    let uu____89351
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89351
                                                                     in
                                                                    (match uu____89343
                                                                    with
                                                                    | 
                                                                    (uu____89365,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89376
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89376
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89381
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89381
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
                                                                  uu____89174
                                                                 in
                                                              (match uu____89160
                                                               with
                                                               | (uu____89402,arg_vars,elim_eqns_or_guards,uu____89405)
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
                                                                    let uu____89432
                                                                    =
                                                                    let uu____89440
                                                                    =
                                                                    let uu____89441
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89442
                                                                    =
                                                                    let uu____89453
                                                                    =
                                                                    let uu____89454
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89454
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89456
                                                                    =
                                                                    let uu____89457
                                                                    =
                                                                    let uu____89462
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89462)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89457
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89453,
                                                                    uu____89456)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89441
                                                                    uu____89442
                                                                     in
                                                                    (uu____89440,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89432
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89477
                                                                    =
                                                                    let uu____89478
                                                                    =
                                                                    let uu____89484
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89484,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89478
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89477
                                                                     in
                                                                    let uu____89487
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89487
                                                                    then
                                                                    let x =
                                                                    let uu____89491
                                                                    =
                                                                    let uu____89497
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89497,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89491
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89502
                                                                    =
                                                                    let uu____89510
                                                                    =
                                                                    let uu____89511
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89512
                                                                    =
                                                                    let uu____89523
                                                                    =
                                                                    let uu____89528
                                                                    =
                                                                    let uu____89531
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89531]
                                                                     in
                                                                    [uu____89528]
                                                                     in
                                                                    let uu____89536
                                                                    =
                                                                    let uu____89537
                                                                    =
                                                                    let uu____89542
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89544
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89542,
                                                                    uu____89544)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89537
                                                                     in
                                                                    (uu____89523,
                                                                    [x],
                                                                    uu____89536)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89511
                                                                    uu____89512
                                                                     in
                                                                    let uu____89565
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89510,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89565)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89502
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89576
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
                                                                    (let uu____89599
                                                                    =
                                                                    let uu____89600
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89600
                                                                    dapp1  in
                                                                    [uu____89599])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89576
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89607
                                                                    =
                                                                    let uu____89615
                                                                    =
                                                                    let uu____89616
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89617
                                                                    =
                                                                    let uu____89628
                                                                    =
                                                                    let uu____89629
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89629
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89631
                                                                    =
                                                                    let uu____89632
                                                                    =
                                                                    let uu____89637
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89637)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89632
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89628,
                                                                    uu____89631)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89616
                                                                    uu____89617
                                                                     in
                                                                    (uu____89615,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89607)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89654 ->
                                                         ((let uu____89656 =
                                                             let uu____89662
                                                               =
                                                               let uu____89664
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89666
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89664
                                                                 uu____89666
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89662)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89656);
                                                          ([], [])))
                                                 in
                                              let uu____89674 =
                                                encode_elim ()  in
                                              (match uu____89674 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89700 =
                                                       let uu____89703 =
                                                         let uu____89706 =
                                                           let uu____89709 =
                                                             let uu____89712
                                                               =
                                                               let uu____89715
                                                                 =
                                                                 let uu____89718
                                                                   =
                                                                   let uu____89719
                                                                    =
                                                                    let uu____89731
                                                                    =
                                                                    let uu____89732
                                                                    =
                                                                    let uu____89734
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89734
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89732
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89731)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89719
                                                                    in
                                                                 [uu____89718]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89715
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89712
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89745 =
                                                             let uu____89748
                                                               =
                                                               let uu____89751
                                                                 =
                                                                 let uu____89754
                                                                   =
                                                                   let uu____89757
                                                                    =
                                                                    let uu____89760
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89765
                                                                    =
                                                                    let uu____89768
                                                                    =
                                                                    let uu____89769
                                                                    =
                                                                    let uu____89777
                                                                    =
                                                                    let uu____89778
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89779
                                                                    =
                                                                    let uu____89790
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89790)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89778
                                                                    uu____89779
                                                                     in
                                                                    (uu____89777,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89769
                                                                     in
                                                                    let uu____89803
                                                                    =
                                                                    let uu____89806
                                                                    =
                                                                    let uu____89807
                                                                    =
                                                                    let uu____89815
                                                                    =
                                                                    let uu____89816
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89817
                                                                    =
                                                                    let uu____89828
                                                                    =
                                                                    let uu____89829
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89829
                                                                    vars'  in
                                                                    let uu____89831
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89828,
                                                                    uu____89831)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89816
                                                                    uu____89817
                                                                     in
                                                                    (uu____89815,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89807
                                                                     in
                                                                    [uu____89806]
                                                                     in
                                                                    uu____89768
                                                                    ::
                                                                    uu____89803
                                                                     in
                                                                    uu____89760
                                                                    ::
                                                                    uu____89765
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89757
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89754
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89751
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89748
                                                              in
                                                           FStar_List.append
                                                             uu____89709
                                                             uu____89745
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89706
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89703
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89700
                                                      in
                                                   let uu____89848 =
                                                     let uu____89849 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89849 g
                                                      in
                                                   (uu____89848, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89883  ->
              fun se  ->
                match uu____89883 with
                | (g,env1) ->
                    let uu____89903 = encode_sigelt env1 se  in
                    (match uu____89903 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89971 =
        match uu____89971 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____90008 ->
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
                 ((let uu____90016 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____90016
                   then
                     let uu____90021 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____90023 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____90025 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____90021 uu____90023 uu____90025
                   else ());
                  (let uu____90030 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____90030 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____90048 =
                         let uu____90056 =
                           let uu____90058 =
                             let uu____90060 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____90060
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____90058  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____90056
                          in
                       (match uu____90048 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____90080 = FStar_Options.log_queries ()
                                 in
                              if uu____90080
                              then
                                let uu____90083 =
                                  let uu____90085 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____90087 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____90089 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____90085 uu____90087 uu____90089
                                   in
                                FStar_Pervasives_Native.Some uu____90083
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90105 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90115 =
                                let uu____90118 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90118  in
                              FStar_List.append uu____90105 uu____90115  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90130,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90150 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90150 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90171 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90171 with | (uu____90198,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90251  ->
              match uu____90251 with
              | (l,uu____90260,uu____90261) ->
                  let uu____90264 =
                    let uu____90276 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90276, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90264))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90309  ->
              match uu____90309 with
              | (l,uu____90320,uu____90321) ->
                  let uu____90324 =
                    let uu____90325 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90328  -> FStar_SMTEncoding_Term.Echo _90328)
                      uu____90325
                     in
                  let uu____90329 =
                    let uu____90332 =
                      let uu____90333 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90333  in
                    [uu____90332]  in
                  uu____90324 :: uu____90329))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90362 =
      let uu____90365 =
        let uu____90366 = FStar_Util.psmap_empty ()  in
        let uu____90381 =
          let uu____90390 = FStar_Util.psmap_empty ()  in (uu____90390, [])
           in
        let uu____90397 =
          let uu____90399 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90399 FStar_Ident.string_of_lid  in
        let uu____90401 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90366;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90381;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90397;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90401
        }  in
      [uu____90365]  in
    FStar_ST.op_Colon_Equals last_env uu____90362
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90445 = FStar_ST.op_Bang last_env  in
      match uu____90445 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90473 ->
          let uu___2175_90476 = e  in
          let uu____90477 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90476.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90476.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90476.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90476.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90476.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90476.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90476.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90477;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90476.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90476.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90485 = FStar_ST.op_Bang last_env  in
    match uu____90485 with
    | [] -> failwith "Empty env stack"
    | uu____90512::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90544  ->
    let uu____90545 = FStar_ST.op_Bang last_env  in
    match uu____90545 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90605  ->
    let uu____90606 = FStar_ST.op_Bang last_env  in
    match uu____90606 with
    | [] -> failwith "Popping an empty stack"
    | uu____90633::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90670  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90723  ->
         let uu____90724 = snapshot_env ()  in
         match uu____90724 with
         | (env_depth,()) ->
             let uu____90746 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90746 with
              | (varops_depth,()) ->
                  let uu____90768 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90768 with
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
        (fun uu____90826  ->
           let uu____90827 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90827 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90922 = snapshot msg  in () 
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
        | (uu____90968::uu____90969,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90977 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90977.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90977.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90977.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90978 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_91005 = elt  in
        let uu____91006 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_91005.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_91005.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____91006;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_91005.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____91026 =
        let uu____91029 =
          let uu____91030 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____91030  in
        let uu____91031 = open_fact_db_tags env  in uu____91029 ::
          uu____91031
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____91026
  
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
      let uu____91058 = encode_sigelt env se  in
      match uu____91058 with
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
                (let uu____91104 =
                   let uu____91107 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91107
                    in
                 match uu____91104 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91122 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91122
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91152 = FStar_Options.log_queries ()  in
        if uu____91152
        then
          let uu____91157 =
            let uu____91158 =
              let uu____91160 =
                let uu____91162 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91162 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91160  in
            FStar_SMTEncoding_Term.Caption uu____91158  in
          uu____91157 :: decls
        else decls  in
      (let uu____91181 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91181
       then
         let uu____91184 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91184
       else ());
      (let env =
         let uu____91190 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91190 tcenv  in
       let uu____91191 = encode_top_level_facts env se  in
       match uu____91191 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91205 =
               let uu____91208 =
                 let uu____91211 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91211
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91208  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91205)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91244 = FStar_Options.log_queries ()  in
          if uu____91244
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91264 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91264.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91264.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91264.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91264.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91264.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91264.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91264.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91264.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91264.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91264.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91269 =
             let uu____91272 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91272
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91269  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91292 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91292
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
          (let uu____91316 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91316
           then
             let uu____91319 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91319
           else ());
          (let env =
             let uu____91327 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91327
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91366  ->
                     fun se  ->
                       match uu____91366 with
                       | (g,env2) ->
                           let uu____91386 = encode_top_level_facts env2 se
                              in
                           (match uu____91386 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91409 =
             encode_signature
               (let uu___2303_91418 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91418.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91418.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91418.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91418.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91418.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91418.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91418.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91418.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91418.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91418.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91409 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91434 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91434
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91440 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91440))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91468  ->
        match uu____91468 with
        | (decls,fvbs) ->
            ((let uu____91482 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91482
              then ()
              else
                (let uu____91487 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91487
                 then
                   let uu____91490 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91490
                 else ()));
             (let env =
                let uu____91498 = get_env name tcenv  in
                FStar_All.pipe_right uu____91498
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91500 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91500
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91514 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91514
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
        (let uu____91576 =
           let uu____91578 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91578.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91576);
        (let env =
           let uu____91580 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91580 tcenv  in
         let uu____91581 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91620 = aux rest  in
                 (match uu____91620 with
                  | (out,rest1) ->
                      let t =
                        let uu____91648 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91648 with
                        | FStar_Pervasives_Native.Some uu____91651 ->
                            let uu____91652 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91652
                              x.FStar_Syntax_Syntax.sort
                        | uu____91653 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91657 =
                        let uu____91660 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91663 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91663.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91663.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91660 :: out  in
                      (uu____91657, rest1))
             | uu____91668 -> ([], bindings)  in
           let uu____91675 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91675 with
           | (closing,bindings) ->
               let uu____91702 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91702, bindings)
            in
         match uu____91581 with
         | (q1,bindings) ->
             let uu____91733 = encode_env_bindings env bindings  in
             (match uu____91733 with
              | (env_decls,env1) ->
                  ((let uu____91755 =
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
                    if uu____91755
                    then
                      let uu____91762 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91762
                    else ());
                   (let uu____91767 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91767 with
                    | (phi,qdecls) ->
                        let uu____91788 =
                          let uu____91793 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91793 phi
                           in
                        (match uu____91788 with
                         | (labels,phi1) ->
                             let uu____91810 = encode_labels labels  in
                             (match uu____91810 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91846 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91846
                                    then
                                      let uu____91851 =
                                        let uu____91852 =
                                          let uu____91854 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91854
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91852
                                         in
                                      [uu____91851]
                                    else []  in
                                  let query_prelude =
                                    let uu____91862 =
                                      let uu____91863 =
                                        let uu____91864 =
                                          let uu____91867 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91874 =
                                            let uu____91877 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91877
                                             in
                                          FStar_List.append uu____91867
                                            uu____91874
                                           in
                                        FStar_List.append env_decls
                                          uu____91864
                                         in
                                      FStar_All.pipe_right uu____91863
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91862
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91887 =
                                      let uu____91895 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91896 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91895,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91896)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91887
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
  