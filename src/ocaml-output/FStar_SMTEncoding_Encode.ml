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
  let uu____68711 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____68711 with
  | (asym,a) ->
      let uu____68722 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____68722 with
       | (xsym,x) ->
           let uu____68733 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____68733 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____68811 =
                      let uu____68823 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____68823, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____68811  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____68843 =
                      let uu____68851 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____68851)  in
                    FStar_SMTEncoding_Util.mkApp uu____68843  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____68870 =
                    let uu____68873 =
                      let uu____68876 =
                        let uu____68879 =
                          let uu____68880 =
                            let uu____68888 =
                              let uu____68889 =
                                let uu____68900 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____68900)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____68889
                               in
                            (uu____68888, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____68880  in
                        let uu____68912 =
                          let uu____68915 =
                            let uu____68916 =
                              let uu____68924 =
                                let uu____68925 =
                                  let uu____68936 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____68936)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____68925
                                 in
                              (uu____68924,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____68916  in
                          [uu____68915]  in
                        uu____68879 :: uu____68912  in
                      xtok_decl :: uu____68876  in
                    xname_decl :: uu____68873  in
                  (xtok1, (FStar_List.length vars), uu____68870)  in
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
                  let uu____69106 =
                    let uu____69127 =
                      let uu____69146 =
                        let uu____69147 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____69147
                         in
                      quant axy uu____69146  in
                    (FStar_Parser_Const.op_Eq, uu____69127)  in
                  let uu____69164 =
                    let uu____69187 =
                      let uu____69208 =
                        let uu____69227 =
                          let uu____69228 =
                            let uu____69229 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____69229  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____69228
                           in
                        quant axy uu____69227  in
                      (FStar_Parser_Const.op_notEq, uu____69208)  in
                    let uu____69246 =
                      let uu____69269 =
                        let uu____69290 =
                          let uu____69309 =
                            let uu____69310 =
                              let uu____69311 =
                                let uu____69316 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____69317 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____69316, uu____69317)  in
                              FStar_SMTEncoding_Util.mkAnd uu____69311  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____69310
                             in
                          quant xy uu____69309  in
                        (FStar_Parser_Const.op_And, uu____69290)  in
                      let uu____69334 =
                        let uu____69357 =
                          let uu____69378 =
                            let uu____69397 =
                              let uu____69398 =
                                let uu____69399 =
                                  let uu____69404 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____69405 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____69404, uu____69405)  in
                                FStar_SMTEncoding_Util.mkOr uu____69399  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____69398
                               in
                            quant xy uu____69397  in
                          (FStar_Parser_Const.op_Or, uu____69378)  in
                        let uu____69422 =
                          let uu____69445 =
                            let uu____69466 =
                              let uu____69485 =
                                let uu____69486 =
                                  let uu____69487 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____69487
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____69486
                                 in
                              quant qx uu____69485  in
                            (FStar_Parser_Const.op_Negation, uu____69466)  in
                          let uu____69504 =
                            let uu____69527 =
                              let uu____69548 =
                                let uu____69567 =
                                  let uu____69568 =
                                    let uu____69569 =
                                      let uu____69574 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____69575 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____69574, uu____69575)  in
                                    FStar_SMTEncoding_Util.mkLT uu____69569
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____69568
                                   in
                                quant xy uu____69567  in
                              (FStar_Parser_Const.op_LT, uu____69548)  in
                            let uu____69592 =
                              let uu____69615 =
                                let uu____69636 =
                                  let uu____69655 =
                                    let uu____69656 =
                                      let uu____69657 =
                                        let uu____69662 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____69663 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____69662, uu____69663)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____69657
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____69656
                                     in
                                  quant xy uu____69655  in
                                (FStar_Parser_Const.op_LTE, uu____69636)  in
                              let uu____69680 =
                                let uu____69703 =
                                  let uu____69724 =
                                    let uu____69743 =
                                      let uu____69744 =
                                        let uu____69745 =
                                          let uu____69750 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____69751 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____69750, uu____69751)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____69745
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____69744
                                       in
                                    quant xy uu____69743  in
                                  (FStar_Parser_Const.op_GT, uu____69724)  in
                                let uu____69768 =
                                  let uu____69791 =
                                    let uu____69812 =
                                      let uu____69831 =
                                        let uu____69832 =
                                          let uu____69833 =
                                            let uu____69838 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____69839 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____69838, uu____69839)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____69833
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____69832
                                         in
                                      quant xy uu____69831  in
                                    (FStar_Parser_Const.op_GTE, uu____69812)
                                     in
                                  let uu____69856 =
                                    let uu____69879 =
                                      let uu____69900 =
                                        let uu____69919 =
                                          let uu____69920 =
                                            let uu____69921 =
                                              let uu____69926 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____69927 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____69926, uu____69927)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____69921
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____69920
                                           in
                                        quant xy uu____69919  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____69900)
                                       in
                                    let uu____69944 =
                                      let uu____69967 =
                                        let uu____69988 =
                                          let uu____70007 =
                                            let uu____70008 =
                                              let uu____70009 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____70009
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____70008
                                             in
                                          quant qx uu____70007  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____69988)
                                         in
                                      let uu____70026 =
                                        let uu____70049 =
                                          let uu____70070 =
                                            let uu____70089 =
                                              let uu____70090 =
                                                let uu____70091 =
                                                  let uu____70096 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____70097 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____70096, uu____70097)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____70091
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____70090
                                               in
                                            quant xy uu____70089  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____70070)
                                           in
                                        let uu____70114 =
                                          let uu____70137 =
                                            let uu____70158 =
                                              let uu____70177 =
                                                let uu____70178 =
                                                  let uu____70179 =
                                                    let uu____70184 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____70185 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____70184,
                                                      uu____70185)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____70179
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____70178
                                                 in
                                              quant xy uu____70177  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____70158)
                                             in
                                          let uu____70202 =
                                            let uu____70225 =
                                              let uu____70246 =
                                                let uu____70265 =
                                                  let uu____70266 =
                                                    let uu____70267 =
                                                      let uu____70272 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____70273 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____70272,
                                                        uu____70273)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____70267
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____70266
                                                   in
                                                quant xy uu____70265  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____70246)
                                               in
                                            let uu____70290 =
                                              let uu____70313 =
                                                let uu____70334 =
                                                  let uu____70353 =
                                                    let uu____70354 =
                                                      let uu____70355 =
                                                        let uu____70360 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____70361 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____70360,
                                                          uu____70361)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____70355
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____70354
                                                     in
                                                  quant xy uu____70353  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____70334)
                                                 in
                                              let uu____70378 =
                                                let uu____70401 =
                                                  let uu____70422 =
                                                    let uu____70441 =
                                                      let uu____70442 =
                                                        let uu____70443 =
                                                          let uu____70448 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____70449 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____70448,
                                                            uu____70449)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____70443
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____70442
                                                       in
                                                    quant xy uu____70441  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____70422)
                                                   in
                                                let uu____70466 =
                                                  let uu____70489 =
                                                    let uu____70510 =
                                                      let uu____70529 =
                                                        let uu____70530 =
                                                          let uu____70531 =
                                                            let uu____70536 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____70537 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____70536,
                                                              uu____70537)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____70531
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____70530
                                                         in
                                                      quant xy uu____70529
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____70510)
                                                     in
                                                  let uu____70554 =
                                                    let uu____70577 =
                                                      let uu____70598 =
                                                        let uu____70617 =
                                                          let uu____70618 =
                                                            let uu____70619 =
                                                              let uu____70624
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____70625
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____70624,
                                                                uu____70625)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____70619
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____70618
                                                           in
                                                        quant xy uu____70617
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____70598)
                                                       in
                                                    let uu____70642 =
                                                      let uu____70665 =
                                                        let uu____70686 =
                                                          let uu____70705 =
                                                            let uu____70706 =
                                                              let uu____70707
                                                                =
                                                                let uu____70712
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____70713
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____70712,
                                                                  uu____70713)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____70707
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____70706
                                                             in
                                                          quant xy
                                                            uu____70705
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____70686)
                                                         in
                                                      let uu____70730 =
                                                        let uu____70753 =
                                                          let uu____70774 =
                                                            let uu____70793 =
                                                              let uu____70794
                                                                =
                                                                let uu____70795
                                                                  =
                                                                  let uu____70800
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____70801
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____70800,
                                                                    uu____70801)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____70795
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____70794
                                                               in
                                                            quant xy
                                                              uu____70793
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____70774)
                                                           in
                                                        let uu____70818 =
                                                          let uu____70841 =
                                                            let uu____70862 =
                                                              let uu____70881
                                                                =
                                                                let uu____70882
                                                                  =
                                                                  let uu____70883
                                                                    =
                                                                    let uu____70888
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70889
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70888,
                                                                    uu____70889)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____70883
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____70882
                                                                 in
                                                              quant xy
                                                                uu____70881
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____70862)
                                                             in
                                                          let uu____70906 =
                                                            let uu____70929 =
                                                              let uu____70950
                                                                =
                                                                let uu____70969
                                                                  =
                                                                  let uu____70970
                                                                    =
                                                                    let uu____70971
                                                                    =
                                                                    let uu____70976
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____70977
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____70976,
                                                                    uu____70977)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____70971
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____70970
                                                                   in
                                                                quant xy
                                                                  uu____70969
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____70950)
                                                               in
                                                            let uu____70994 =
                                                              let uu____71017
                                                                =
                                                                let uu____71038
                                                                  =
                                                                  let uu____71057
                                                                    =
                                                                    let uu____71058
                                                                    =
                                                                    let uu____71059
                                                                    =
                                                                    let uu____71064
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____71065
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____71064,
                                                                    uu____71065)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____71059
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____71058
                                                                     in
                                                                  quant xy
                                                                    uu____71057
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____71038)
                                                                 in
                                                              let uu____71082
                                                                =
                                                                let uu____71105
                                                                  =
                                                                  let uu____71126
                                                                    =
                                                                    let uu____71145
                                                                    =
                                                                    let uu____71146
                                                                    =
                                                                    let uu____71147
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____71147
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____71146
                                                                     in
                                                                    quant qx
                                                                    uu____71145
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____71126)
                                                                   in
                                                                [uu____71105]
                                                                 in
                                                              uu____71017 ::
                                                                uu____71082
                                                               in
                                                            uu____70929 ::
                                                              uu____70994
                                                             in
                                                          uu____70841 ::
                                                            uu____70906
                                                           in
                                                        uu____70753 ::
                                                          uu____70818
                                                         in
                                                      uu____70665 ::
                                                        uu____70730
                                                       in
                                                    uu____70577 ::
                                                      uu____70642
                                                     in
                                                  uu____70489 :: uu____70554
                                                   in
                                                uu____70401 :: uu____70466
                                                 in
                                              uu____70313 :: uu____70378  in
                                            uu____70225 :: uu____70290  in
                                          uu____70137 :: uu____70202  in
                                        uu____70049 :: uu____70114  in
                                      uu____69967 :: uu____70026  in
                                    uu____69879 :: uu____69944  in
                                  uu____69791 :: uu____69856  in
                                uu____69703 :: uu____69768  in
                              uu____69615 :: uu____69680  in
                            uu____69527 :: uu____69592  in
                          uu____69445 :: uu____69504  in
                        uu____69357 :: uu____69422  in
                      uu____69269 :: uu____69334  in
                    uu____69187 :: uu____69246  in
                  uu____69106 :: uu____69164  in
                let mk1 l v1 =
                  let uu____71686 =
                    let uu____71698 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____71788  ->
                              match uu____71788 with
                              | (l',uu____71809) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____71698
                      (FStar_Option.map
                         (fun uu____71908  ->
                            match uu____71908 with
                            | (uu____71936,b) ->
                                let uu____71970 = FStar_Ident.range_of_lid l
                                   in
                                b uu____71970 v1))
                     in
                  FStar_All.pipe_right uu____71686 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____72053  ->
                          match uu____72053 with
                          | (l',uu____72074) -> FStar_Ident.lid_equals l l'))
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
          let uu____72148 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____72148 with
          | (xxsym,xx) ->
              let uu____72159 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____72159 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____72175 =
                     let uu____72183 =
                       let uu____72184 =
                         let uu____72195 =
                           let uu____72196 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____72206 =
                             let uu____72217 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____72217 :: vars  in
                           uu____72196 :: uu____72206  in
                         let uu____72243 =
                           let uu____72244 =
                             let uu____72249 =
                               let uu____72250 =
                                 let uu____72255 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____72255)  in
                               FStar_SMTEncoding_Util.mkEq uu____72250  in
                             (xx_has_type, uu____72249)  in
                           FStar_SMTEncoding_Util.mkImp uu____72244  in
                         ([[xx_has_type]], uu____72195, uu____72243)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____72184  in
                     let uu____72268 =
                       let uu____72270 =
                         let uu____72272 =
                           let uu____72274 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____72274  in
                         Prims.op_Hat module_name uu____72272  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____72270
                        in
                     (uu____72183,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____72268)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____72175)
  
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
    let uu____72330 =
      let uu____72332 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____72332  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____72330  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____72354 =
      let uu____72355 =
        let uu____72363 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____72363, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72355  in
    let uu____72368 =
      let uu____72371 =
        let uu____72372 =
          let uu____72380 =
            let uu____72381 =
              let uu____72392 =
                let uu____72393 =
                  let uu____72398 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____72398)  in
                FStar_SMTEncoding_Util.mkImp uu____72393  in
              ([[typing_pred]], [xx], uu____72392)  in
            let uu____72423 =
              let uu____72438 = FStar_TypeChecker_Env.get_range env  in
              let uu____72439 = mkForall_fuel1 env  in
              uu____72439 uu____72438  in
            uu____72423 uu____72381  in
          (uu____72380, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72372  in
      [uu____72371]  in
    uu____72354 :: uu____72368  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____72486 =
      let uu____72487 =
        let uu____72495 =
          let uu____72496 = FStar_TypeChecker_Env.get_range env  in
          let uu____72497 =
            let uu____72508 =
              let uu____72513 =
                let uu____72516 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____72516]  in
              [uu____72513]  in
            let uu____72521 =
              let uu____72522 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72522 tt  in
            (uu____72508, [bb], uu____72521)  in
          FStar_SMTEncoding_Term.mkForall uu____72496 uu____72497  in
        (uu____72495, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72487  in
    let uu____72547 =
      let uu____72550 =
        let uu____72551 =
          let uu____72559 =
            let uu____72560 =
              let uu____72571 =
                let uu____72572 =
                  let uu____72577 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____72577)  in
                FStar_SMTEncoding_Util.mkImp uu____72572  in
              ([[typing_pred]], [xx], uu____72571)  in
            let uu____72604 =
              let uu____72619 = FStar_TypeChecker_Env.get_range env  in
              let uu____72620 = mkForall_fuel1 env  in
              uu____72620 uu____72619  in
            uu____72604 uu____72560  in
          (uu____72559, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72551  in
      [uu____72550]  in
    uu____72486 :: uu____72547  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____72663 =
        let uu____72664 =
          let uu____72670 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____72670, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____72664  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____72663  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____72684 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____72684  in
    let uu____72689 =
      let uu____72690 =
        let uu____72698 =
          let uu____72699 = FStar_TypeChecker_Env.get_range env  in
          let uu____72700 =
            let uu____72711 =
              let uu____72716 =
                let uu____72719 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____72719]  in
              [uu____72716]  in
            let uu____72724 =
              let uu____72725 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____72725 tt  in
            (uu____72711, [bb], uu____72724)  in
          FStar_SMTEncoding_Term.mkForall uu____72699 uu____72700  in
        (uu____72698, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____72690  in
    let uu____72750 =
      let uu____72753 =
        let uu____72754 =
          let uu____72762 =
            let uu____72763 =
              let uu____72774 =
                let uu____72775 =
                  let uu____72780 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____72780)  in
                FStar_SMTEncoding_Util.mkImp uu____72775  in
              ([[typing_pred]], [xx], uu____72774)  in
            let uu____72807 =
              let uu____72822 = FStar_TypeChecker_Env.get_range env  in
              let uu____72823 = mkForall_fuel1 env  in
              uu____72823 uu____72822  in
            uu____72807 uu____72763  in
          (uu____72762, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____72754  in
      let uu____72845 =
        let uu____72848 =
          let uu____72849 =
            let uu____72857 =
              let uu____72858 =
                let uu____72869 =
                  let uu____72870 =
                    let uu____72875 =
                      let uu____72876 =
                        let uu____72879 =
                          let uu____72882 =
                            let uu____72885 =
                              let uu____72886 =
                                let uu____72891 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____72892 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____72891, uu____72892)  in
                              FStar_SMTEncoding_Util.mkGT uu____72886  in
                            let uu____72894 =
                              let uu____72897 =
                                let uu____72898 =
                                  let uu____72903 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____72904 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____72903, uu____72904)  in
                                FStar_SMTEncoding_Util.mkGTE uu____72898  in
                              let uu____72906 =
                                let uu____72909 =
                                  let uu____72910 =
                                    let uu____72915 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____72916 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____72915, uu____72916)  in
                                  FStar_SMTEncoding_Util.mkLT uu____72910  in
                                [uu____72909]  in
                              uu____72897 :: uu____72906  in
                            uu____72885 :: uu____72894  in
                          typing_pred_y :: uu____72882  in
                        typing_pred :: uu____72879  in
                      FStar_SMTEncoding_Util.mk_and_l uu____72876  in
                    (uu____72875, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____72870  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____72869)
                 in
              let uu____72949 =
                let uu____72964 = FStar_TypeChecker_Env.get_range env  in
                let uu____72965 = mkForall_fuel1 env  in
                uu____72965 uu____72964  in
              uu____72949 uu____72858  in
            (uu____72857,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____72849  in
        [uu____72848]  in
      uu____72753 :: uu____72845  in
    uu____72689 :: uu____72750  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____73008 =
        let uu____73009 =
          let uu____73015 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____73015, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____73009  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____73008  in
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
      let uu____73031 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____73031  in
    let uu____73036 =
      let uu____73037 =
        let uu____73045 =
          let uu____73046 = FStar_TypeChecker_Env.get_range env  in
          let uu____73047 =
            let uu____73058 =
              let uu____73063 =
                let uu____73066 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____73066]  in
              [uu____73063]  in
            let uu____73071 =
              let uu____73072 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____73072 tt  in
            (uu____73058, [bb], uu____73071)  in
          FStar_SMTEncoding_Term.mkForall uu____73046 uu____73047  in
        (uu____73045, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73037  in
    let uu____73097 =
      let uu____73100 =
        let uu____73101 =
          let uu____73109 =
            let uu____73110 =
              let uu____73121 =
                let uu____73122 =
                  let uu____73127 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____73127)  in
                FStar_SMTEncoding_Util.mkImp uu____73122  in
              ([[typing_pred]], [xx], uu____73121)  in
            let uu____73154 =
              let uu____73169 = FStar_TypeChecker_Env.get_range env  in
              let uu____73170 = mkForall_fuel1 env  in
              uu____73170 uu____73169  in
            uu____73154 uu____73110  in
          (uu____73109, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____73101  in
      let uu____73192 =
        let uu____73195 =
          let uu____73196 =
            let uu____73204 =
              let uu____73205 =
                let uu____73216 =
                  let uu____73217 =
                    let uu____73222 =
                      let uu____73223 =
                        let uu____73226 =
                          let uu____73229 =
                            let uu____73232 =
                              let uu____73233 =
                                let uu____73238 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____73239 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____73238, uu____73239)  in
                              FStar_SMTEncoding_Util.mkGT uu____73233  in
                            let uu____73241 =
                              let uu____73244 =
                                let uu____73245 =
                                  let uu____73250 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____73251 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____73250, uu____73251)  in
                                FStar_SMTEncoding_Util.mkGTE uu____73245  in
                              let uu____73253 =
                                let uu____73256 =
                                  let uu____73257 =
                                    let uu____73262 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____73263 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____73262, uu____73263)  in
                                  FStar_SMTEncoding_Util.mkLT uu____73257  in
                                [uu____73256]  in
                              uu____73244 :: uu____73253  in
                            uu____73232 :: uu____73241  in
                          typing_pred_y :: uu____73229  in
                        typing_pred :: uu____73226  in
                      FStar_SMTEncoding_Util.mk_and_l uu____73223  in
                    (uu____73222, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____73217  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____73216)
                 in
              let uu____73296 =
                let uu____73311 = FStar_TypeChecker_Env.get_range env  in
                let uu____73312 = mkForall_fuel1 env  in
                uu____73312 uu____73311  in
              uu____73296 uu____73205  in
            (uu____73204,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____73196  in
        [uu____73195]  in
      uu____73100 :: uu____73192  in
    uu____73036 :: uu____73097  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____73359 =
      let uu____73360 =
        let uu____73368 =
          let uu____73369 = FStar_TypeChecker_Env.get_range env  in
          let uu____73370 =
            let uu____73381 =
              let uu____73386 =
                let uu____73389 = FStar_SMTEncoding_Term.boxString b  in
                [uu____73389]  in
              [uu____73386]  in
            let uu____73394 =
              let uu____73395 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____73395 tt  in
            (uu____73381, [bb], uu____73394)  in
          FStar_SMTEncoding_Term.mkForall uu____73369 uu____73370  in
        (uu____73368, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73360  in
    let uu____73420 =
      let uu____73423 =
        let uu____73424 =
          let uu____73432 =
            let uu____73433 =
              let uu____73444 =
                let uu____73445 =
                  let uu____73450 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____73450)  in
                FStar_SMTEncoding_Util.mkImp uu____73445  in
              ([[typing_pred]], [xx], uu____73444)  in
            let uu____73477 =
              let uu____73492 = FStar_TypeChecker_Env.get_range env  in
              let uu____73493 = mkForall_fuel1 env  in
              uu____73493 uu____73492  in
            uu____73477 uu____73433  in
          (uu____73432, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____73424  in
      [uu____73423]  in
    uu____73359 :: uu____73420  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____73540 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____73540]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____73570 =
      let uu____73571 =
        let uu____73579 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____73579, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73571  in
    [uu____73570]  in
  let mk_and_interp env conj uu____73602 =
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
    let uu____73631 =
      let uu____73632 =
        let uu____73640 =
          let uu____73641 = FStar_TypeChecker_Env.get_range env  in
          let uu____73642 =
            let uu____73653 =
              let uu____73654 =
                let uu____73659 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____73659, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73654  in
            ([[l_and_a_b]], [aa; bb], uu____73653)  in
          FStar_SMTEncoding_Term.mkForall uu____73641 uu____73642  in
        (uu____73640, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73632  in
    [uu____73631]  in
  let mk_or_interp env disj uu____73714 =
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
    let uu____73743 =
      let uu____73744 =
        let uu____73752 =
          let uu____73753 = FStar_TypeChecker_Env.get_range env  in
          let uu____73754 =
            let uu____73765 =
              let uu____73766 =
                let uu____73771 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____73771, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73766  in
            ([[l_or_a_b]], [aa; bb], uu____73765)  in
          FStar_SMTEncoding_Term.mkForall uu____73753 uu____73754  in
        (uu____73752, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73744  in
    [uu____73743]  in
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
    let uu____73849 =
      let uu____73850 =
        let uu____73858 =
          let uu____73859 = FStar_TypeChecker_Env.get_range env  in
          let uu____73860 =
            let uu____73871 =
              let uu____73872 =
                let uu____73877 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73877, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73872  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____73871)  in
          FStar_SMTEncoding_Term.mkForall uu____73859 uu____73860  in
        (uu____73858, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73850  in
    [uu____73849]  in
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
    let uu____73967 =
      let uu____73968 =
        let uu____73976 =
          let uu____73977 = FStar_TypeChecker_Env.get_range env  in
          let uu____73978 =
            let uu____73989 =
              let uu____73990 =
                let uu____73995 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____73995, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____73990  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____73989)  in
          FStar_SMTEncoding_Term.mkForall uu____73977 uu____73978  in
        (uu____73976, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____73968  in
    [uu____73967]  in
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
    let uu____74095 =
      let uu____74096 =
        let uu____74104 =
          let uu____74105 = FStar_TypeChecker_Env.get_range env  in
          let uu____74106 =
            let uu____74117 =
              let uu____74118 =
                let uu____74123 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____74123, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____74118  in
            ([[l_imp_a_b]], [aa; bb], uu____74117)  in
          FStar_SMTEncoding_Term.mkForall uu____74105 uu____74106  in
        (uu____74104, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____74096  in
    [uu____74095]  in
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
    let uu____74207 =
      let uu____74208 =
        let uu____74216 =
          let uu____74217 = FStar_TypeChecker_Env.get_range env  in
          let uu____74218 =
            let uu____74229 =
              let uu____74230 =
                let uu____74235 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____74235, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____74230  in
            ([[l_iff_a_b]], [aa; bb], uu____74229)  in
          FStar_SMTEncoding_Term.mkForall uu____74217 uu____74218  in
        (uu____74216, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____74208  in
    [uu____74207]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____74306 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____74306  in
    let uu____74311 =
      let uu____74312 =
        let uu____74320 =
          let uu____74321 = FStar_TypeChecker_Env.get_range env  in
          let uu____74322 =
            let uu____74333 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____74333)  in
          FStar_SMTEncoding_Term.mkForall uu____74321 uu____74322  in
        (uu____74320, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____74312  in
    [uu____74311]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____74386 =
      let uu____74387 =
        let uu____74395 =
          let uu____74396 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____74396 range_ty  in
        let uu____74397 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____74395, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____74397)
         in
      FStar_SMTEncoding_Util.mkAssume uu____74387  in
    [uu____74386]  in
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
        let uu____74443 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____74443 x1 t  in
      let uu____74445 = FStar_TypeChecker_Env.get_range env  in
      let uu____74446 =
        let uu____74457 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____74457)  in
      FStar_SMTEncoding_Term.mkForall uu____74445 uu____74446  in
    let uu____74482 =
      let uu____74483 =
        let uu____74491 =
          let uu____74492 = FStar_TypeChecker_Env.get_range env  in
          let uu____74493 =
            let uu____74504 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____74504)  in
          FStar_SMTEncoding_Term.mkForall uu____74492 uu____74493  in
        (uu____74491,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____74483  in
    [uu____74482]  in
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
    let uu____74565 =
      let uu____74566 =
        let uu____74574 =
          let uu____74575 = FStar_TypeChecker_Env.get_range env  in
          let uu____74576 =
            let uu____74592 =
              let uu____74593 =
                let uu____74598 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____74599 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____74598, uu____74599)  in
              FStar_SMTEncoding_Util.mkAnd uu____74593  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____74592)
             in
          FStar_SMTEncoding_Term.mkForall' uu____74575 uu____74576  in
        (uu____74574,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____74566  in
    [uu____74565]  in
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
          let uu____75157 =
            FStar_Util.find_opt
              (fun uu____75195  ->
                 match uu____75195 with
                 | (l,uu____75211) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____75157 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____75254,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____75315 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____75315 with
        | (form,decls) ->
            let uu____75324 =
              let uu____75327 =
                let uu____75330 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____75330]  in
              FStar_All.pipe_right uu____75327
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____75324
  
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
              let uu____75389 =
                ((let uu____75393 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____75393) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____75389
              then
                let arg_sorts =
                  let uu____75405 =
                    let uu____75406 = FStar_Syntax_Subst.compress t_norm  in
                    uu____75406.FStar_Syntax_Syntax.n  in
                  match uu____75405 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75412) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____75450  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____75457 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____75459 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____75459 with
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
                    let uu____75491 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____75491, env1)
              else
                (let uu____75496 = prims.is lid  in
                 if uu____75496
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____75505 = prims.mk lid vname  in
                   match uu____75505 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____75529 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____75529, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____75538 =
                      let uu____75557 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____75557 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____75585 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____75585
                            then
                              let uu____75590 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_75593 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_75593.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_75593.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_75593.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_75593.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_75593.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_75593.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_75593.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_75593.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_75593.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_75593.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_75593.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_75593.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_75593.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_75593.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_75593.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_75593.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_75593.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_75593.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_75593.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_75593.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_75593.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_75593.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_75593.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_75593.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_75593.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_75593.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_75593.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_75593.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_75593.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_75593.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_75593.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_75593.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_75593.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_75593.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_75593.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_75593.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_75593.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_75593.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_75593.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_75593.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_75593.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_75593.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____75590
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____75616 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____75616)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____75538 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_75722  ->
                                  match uu___639_75722 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____75726 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75726 with
                                       | (uu____75759,xxv) ->
                                           let xx =
                                             let uu____75798 =
                                               let uu____75799 =
                                                 let uu____75805 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75805,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75799
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75798
                                              in
                                           let uu____75808 =
                                             let uu____75809 =
                                               let uu____75817 =
                                                 let uu____75818 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75819 =
                                                   let uu____75830 =
                                                     let uu____75831 =
                                                       let uu____75836 =
                                                         let uu____75837 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____75837
                                                          in
                                                       (vapp, uu____75836)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____75831
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75830)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75818 uu____75819
                                                  in
                                               (uu____75817,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75809
                                              in
                                           [uu____75808])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____75852 =
                                        FStar_Util.prefix vars  in
                                      (match uu____75852 with
                                       | (uu____75885,xxv) ->
                                           let xx =
                                             let uu____75924 =
                                               let uu____75925 =
                                                 let uu____75931 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____75931,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____75925
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____75924
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
                                           let uu____75942 =
                                             let uu____75943 =
                                               let uu____75951 =
                                                 let uu____75952 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____75953 =
                                                   let uu____75964 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____75964)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____75952 uu____75953
                                                  in
                                               (uu____75951,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____75943
                                              in
                                           [uu____75942])
                                  | uu____75977 -> []))
                           in
                        let uu____75978 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____75978 with
                         | (vars,guards,env',decls1,uu____76003) ->
                             let uu____76016 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____76029 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____76029, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____76033 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____76033 with
                                    | (g,ds) ->
                                        let uu____76046 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____76046,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____76016 with
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
                                  let should_thunk uu____76069 =
                                    let is_type1 t =
                                      let uu____76077 =
                                        let uu____76078 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____76078.FStar_Syntax_Syntax.n  in
                                      match uu____76077 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____76082 -> true
                                      | uu____76084 -> false  in
                                    let is_squash1 t =
                                      let uu____76093 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____76093 with
                                      | (head1,uu____76112) ->
                                          let uu____76137 =
                                            let uu____76138 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____76138.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____76137 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____76143;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____76144;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____76146;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____76147;_};_},uu____76148)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____76156 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____76161 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____76161))
                                       &&
                                       (let uu____76167 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____76167))
                                      &&
                                      (let uu____76170 = is_type1 t_norm  in
                                       Prims.op_Negation uu____76170)
                                     in
                                  let uu____76172 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____76231 -> (false, vars)  in
                                  (match uu____76172 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____76281 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____76281 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____76313 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____76322 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____76322
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____76333 ->
                                                  let uu____76342 =
                                                    let uu____76350 =
                                                      get_vtok ()  in
                                                    (uu____76350, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____76342
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____76357 =
                                                let uu____76365 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____76365)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____76357
                                               in
                                            let uu____76379 =
                                              let vname_decl =
                                                let uu____76387 =
                                                  let uu____76399 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____76399,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____76387
                                                 in
                                              let uu____76410 =
                                                let env2 =
                                                  let uu___1026_76416 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_76416.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____76417 =
                                                  let uu____76419 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____76419
                                                   in
                                                if uu____76417
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____76410 with
                                              | (tok_typing,decls2) ->
                                                  let uu____76436 =
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
                                                        let uu____76462 =
                                                          let uu____76465 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76465
                                                           in
                                                        let uu____76472 =
                                                          let uu____76473 =
                                                            let uu____76476 =
                                                              let uu____76477
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____76477
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _76481  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _76481)
                                                              uu____76476
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____76473
                                                           in
                                                        (uu____76462,
                                                          uu____76472)
                                                    | uu____76484 when
                                                        thunked ->
                                                        let uu____76495 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____76495
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____76510
                                                                 =
                                                                 let uu____76518
                                                                   =
                                                                   let uu____76521
                                                                    =
                                                                    let uu____76524
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____76524]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____76521
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____76518)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____76510
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____76532
                                                               =
                                                               let uu____76540
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____76540,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____76532
                                                              in
                                                           let uu____76545 =
                                                             let uu____76548
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____76548
                                                              in
                                                           (uu____76545,
                                                             env1))
                                                    | uu____76557 ->
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
                                                          let uu____76581 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____76582 =
                                                            let uu____76593 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____76593)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____76581
                                                            uu____76582
                                                           in
                                                        let name_tok_corr =
                                                          let uu____76603 =
                                                            let uu____76611 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____76611,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____76603
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
                                                            let uu____76622 =
                                                              let uu____76623
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____76623]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____76622
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____76650 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76651 =
                                                              let uu____76662
                                                                =
                                                                let uu____76663
                                                                  =
                                                                  let uu____76668
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____76669
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____76668,
                                                                    uu____76669)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____76663
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____76662)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____76650
                                                              uu____76651
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____76698 =
                                                          let uu____76701 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76701
                                                           in
                                                        (uu____76698, env1)
                                                     in
                                                  (match uu____76436 with
                                                   | (tok_decl,env2) ->
                                                       let uu____76722 =
                                                         let uu____76725 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____76725
                                                           tok_decl
                                                          in
                                                       (uu____76722, env2))
                                               in
                                            (match uu____76379 with
                                             | (decls2,env2) ->
                                                 let uu____76744 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____76754 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____76754 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____76769 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____76769, decls)
                                                    in
                                                 (match uu____76744 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____76784 =
                                                          let uu____76792 =
                                                            let uu____76793 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76794 =
                                                              let uu____76805
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____76805)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____76793
                                                              uu____76794
                                                             in
                                                          (uu____76792,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____76784
                                                         in
                                                      let freshness =
                                                        let uu____76821 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____76821
                                                        then
                                                          let uu____76829 =
                                                            let uu____76830 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____76831 =
                                                              let uu____76844
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____76851
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____76844,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____76851)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____76830
                                                              uu____76831
                                                             in
                                                          let uu____76857 =
                                                            let uu____76860 =
                                                              let uu____76861
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____76861
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____76860]  in
                                                          uu____76829 ::
                                                            uu____76857
                                                        else []  in
                                                      let g =
                                                        let uu____76867 =
                                                          let uu____76870 =
                                                            let uu____76873 =
                                                              let uu____76876
                                                                =
                                                                let uu____76879
                                                                  =
                                                                  let uu____76882
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____76882
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____76879
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____76876
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____76873
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____76870
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____76867
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
          let uu____76922 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____76922 with
          | FStar_Pervasives_Native.None  ->
              let uu____76933 = encode_free_var false env x t t_norm []  in
              (match uu____76933 with
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
            let uu____76996 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____76996 with
            | (decls,env1) ->
                let uu____77007 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____77007
                then
                  let uu____77014 =
                    let uu____77015 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____77015  in
                  (uu____77014, env1)
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
             (fun uu____77071  ->
                fun lb  ->
                  match uu____77071 with
                  | (decls,env1) ->
                      let uu____77091 =
                        let uu____77096 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____77096
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____77091 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____77125 = FStar_Syntax_Util.head_and_args t  in
    match uu____77125 with
    | (hd1,args) ->
        let uu____77169 =
          let uu____77170 = FStar_Syntax_Util.un_uinst hd1  in
          uu____77170.FStar_Syntax_Syntax.n  in
        (match uu____77169 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____77176,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____77200 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____77211 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_77219 = en  in
    let uu____77220 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_77219.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_77219.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_77219.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_77219.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_77219.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_77219.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_77219.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_77219.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_77219.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_77219.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____77220
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____77250  ->
      fun quals  ->
        match uu____77250 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____77355 = FStar_Util.first_N nbinders formals  in
              match uu____77355 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____77452  ->
                         fun uu____77453  ->
                           match (uu____77452, uu____77453) with
                           | ((formal,uu____77479),(binder,uu____77481)) ->
                               let uu____77502 =
                                 let uu____77509 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____77509)  in
                               FStar_Syntax_Syntax.NT uu____77502) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____77523 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____77564  ->
                              match uu____77564 with
                              | (x,i) ->
                                  let uu____77583 =
                                    let uu___1139_77584 = x  in
                                    let uu____77585 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_77584.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_77584.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____77585
                                    }  in
                                  (uu____77583, i)))
                       in
                    FStar_All.pipe_right uu____77523
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____77609 =
                      let uu____77614 = FStar_Syntax_Subst.compress body  in
                      let uu____77615 =
                        let uu____77616 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____77616
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____77614
                        uu____77615
                       in
                    uu____77609 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_77665 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_77665.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_77665.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_77665.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_77665.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_77665.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_77665.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_77665.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_77665.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_77665.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_77665.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_77665.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_77665.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_77665.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_77665.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_77665.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_77665.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_77665.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_77665.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_77665.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_77665.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_77665.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_77665.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_77665.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_77665.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_77665.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_77665.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_77665.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_77665.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_77665.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_77665.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_77665.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_77665.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_77665.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_77665.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_77665.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_77665.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_77665.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_77665.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_77665.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_77665.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_77665.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_77665.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____77737  ->
                       fun uu____77738  ->
                         match (uu____77737, uu____77738) with
                         | ((x,uu____77764),(b,uu____77766)) ->
                             let uu____77787 =
                               let uu____77794 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____77794)  in
                             FStar_Syntax_Syntax.NT uu____77787) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____77819 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____77819
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____77848 ->
                    let uu____77855 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____77855
                | uu____77856 when Prims.op_Negation norm1 ->
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
                | uu____77859 ->
                    let uu____77860 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____77860)
                 in
              let aux t1 e1 =
                let uu____77902 = FStar_Syntax_Util.abs_formals e1  in
                match uu____77902 with
                | (binders,body,lopt) ->
                    let uu____77934 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____77950 -> arrow_formals_comp_norm false t1  in
                    (match uu____77934 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____77984 =
                           if nformals < nbinders
                           then
                             let uu____78018 =
                               FStar_Util.first_N nformals binders  in
                             match uu____78018 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____78098 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____78098)
                           else
                             if nformals > nbinders
                             then
                               (let uu____78128 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____78128 with
                                | (binders1,body1) ->
                                    let uu____78181 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____78181))
                             else
                               (let uu____78194 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____78194))
                            in
                         (match uu____77984 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____78254 = aux t e  in
              match uu____78254 with
              | (binders,body,comp) ->
                  let uu____78300 =
                    let uu____78311 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____78311
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____78326 = aux comp1 body1  in
                      match uu____78326 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____78300 with
                   | (binders1,body1,comp1) ->
                       let uu____78409 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____78409, comp1))
               in
            (try
               (fun uu___1216_78436  ->
                  match () with
                  | () ->
                      let uu____78443 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____78443
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____78459 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____78522  ->
                                   fun lb  ->
                                     match uu____78522 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____78577 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____78577
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____78583 =
                                             let uu____78592 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____78592
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____78583 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____78459 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____78733;
                                    FStar_Syntax_Syntax.lbeff = uu____78734;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____78736;
                                    FStar_Syntax_Syntax.lbpos = uu____78737;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____78761 =
                                     let uu____78768 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____78768 with
                                     | (tcenv',uu____78784,e_t) ->
                                         let uu____78790 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____78801 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____78790 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_78818 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_78818.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____78761 with
                                    | (env',e1,t_norm1) ->
                                        let uu____78828 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____78828 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____78848 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____78848
                                               then
                                                 let uu____78853 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____78856 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____78853 uu____78856
                                               else ());
                                              (let uu____78861 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____78861 with
                                               | (vars,_guards,env'1,binder_decls,uu____78888)
                                                   ->
                                                   let uu____78901 =
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
                                                         let uu____78918 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____78918
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____78940 =
                                                          let uu____78941 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____78942 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____78941 fvb
                                                            uu____78942
                                                           in
                                                        (vars, uu____78940))
                                                      in
                                                   (match uu____78901 with
                                                    | (vars1,app) ->
                                                        let uu____78953 =
                                                          let is_logical =
                                                            let uu____78966 =
                                                              let uu____78967
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____78967.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____78966
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____78973 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____78977 =
                                                              let uu____78978
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____78978
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____78977
                                                              (fun lid  ->
                                                                 let uu____78987
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____78987
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____78988 =
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
                                                          if uu____78988
                                                          then
                                                            let uu____79004 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____79005 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____79004,
                                                              uu____79005)
                                                          else
                                                            (let uu____79016
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____79016))
                                                           in
                                                        (match uu____78953
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____79040
                                                                 =
                                                                 let uu____79048
                                                                   =
                                                                   let uu____79049
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____79050
                                                                    =
                                                                    let uu____79061
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____79061)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____79049
                                                                    uu____79050
                                                                    in
                                                                 let uu____79070
                                                                   =
                                                                   let uu____79071
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____79071
                                                                    in
                                                                 (uu____79048,
                                                                   uu____79070,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____79040
                                                                in
                                                             let uu____79077
                                                               =
                                                               let uu____79080
                                                                 =
                                                                 let uu____79083
                                                                   =
                                                                   let uu____79086
                                                                    =
                                                                    let uu____79089
                                                                    =
                                                                    let uu____79092
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____79092
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____79089
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____79086
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____79083
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____79080
                                                                in
                                                             (uu____79077,
                                                               env2)))))))
                               | uu____79101 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____79161 =
                                   let uu____79167 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____79167,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____79161  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____79173 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____79226  ->
                                         fun fvb  ->
                                           match uu____79226 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____79281 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____79281
                                                  in
                                               let gtok =
                                                 let uu____79285 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____79285
                                                  in
                                               let env4 =
                                                 let uu____79288 =
                                                   let uu____79291 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _79297  ->
                                                        FStar_Pervasives_Native.Some
                                                          _79297) uu____79291
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____79288
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____79173 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____79417
                                     t_norm uu____79419 =
                                     match (uu____79417, uu____79419) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____79449;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____79450;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____79452;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____79453;_})
                                         ->
                                         let uu____79480 =
                                           let uu____79487 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____79487 with
                                           | (tcenv',uu____79503,e_t) ->
                                               let uu____79509 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____79520 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____79509 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_79537 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_79537.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____79480 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____79550 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____79550
                                                then
                                                  let uu____79555 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____79557 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____79559 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____79555 uu____79557
                                                    uu____79559
                                                else ());
                                               (let uu____79564 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____79564 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____79591 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____79591 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____79613 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____79613
                                                           then
                                                             let uu____79618
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____79620
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____79623
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____79625
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____79618
                                                               uu____79620
                                                               uu____79623
                                                               uu____79625
                                                           else ());
                                                          (let uu____79630 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____79630
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____79659)
                                                               ->
                                                               let uu____79672
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____79685
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____79685,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____79689
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____79689
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____79702
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____79702,
                                                                    decls0))
                                                                  in
                                                               (match uu____79672
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
                                                                    let uu____79723
                                                                    =
                                                                    let uu____79735
                                                                    =
                                                                    let uu____79738
                                                                    =
                                                                    let uu____79741
                                                                    =
                                                                    let uu____79744
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____79744
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____79741
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____79738
                                                                     in
                                                                    (g,
                                                                    uu____79735,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____79723
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
                                                                    let uu____79774
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____79774
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
                                                                    let uu____79789
                                                                    =
                                                                    let uu____79792
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____79792
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79789
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____79798
                                                                    =
                                                                    let uu____79801
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____79801
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79798
                                                                     in
                                                                    let uu____79806
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____79806
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____79822
                                                                    =
                                                                    let uu____79830
                                                                    =
                                                                    let uu____79831
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79832
                                                                    =
                                                                    let uu____79848
                                                                    =
                                                                    let uu____79849
                                                                    =
                                                                    let uu____79854
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____79854)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____79849
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79848)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____79831
                                                                    uu____79832
                                                                     in
                                                                    let uu____79868
                                                                    =
                                                                    let uu____79869
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79869
                                                                     in
                                                                    (uu____79830,
                                                                    uu____79868,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79822
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____79876
                                                                    =
                                                                    let uu____79884
                                                                    =
                                                                    let uu____79885
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79886
                                                                    =
                                                                    let uu____79897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____79897)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79885
                                                                    uu____79886
                                                                     in
                                                                    (uu____79884,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79876
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____79911
                                                                    =
                                                                    let uu____79919
                                                                    =
                                                                    let uu____79920
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79921
                                                                    =
                                                                    let uu____79932
                                                                    =
                                                                    let uu____79933
                                                                    =
                                                                    let uu____79938
                                                                    =
                                                                    let uu____79939
                                                                    =
                                                                    let uu____79942
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____79942
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____79939
                                                                     in
                                                                    (gsapp,
                                                                    uu____79938)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____79933
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79932)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79920
                                                                    uu____79921
                                                                     in
                                                                    (uu____79919,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79911
                                                                     in
                                                                    let uu____79956
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
                                                                    let uu____79968
                                                                    =
                                                                    let uu____79969
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____79969
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____79968
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____79971
                                                                    =
                                                                    let uu____79979
                                                                    =
                                                                    let uu____79980
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____79981
                                                                    =
                                                                    let uu____79992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____79992)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____79980
                                                                    uu____79981
                                                                     in
                                                                    (uu____79979,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____79971
                                                                     in
                                                                    let uu____80005
                                                                    =
                                                                    let uu____80014
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____80014
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____80029
                                                                    =
                                                                    let uu____80032
                                                                    =
                                                                    let uu____80033
                                                                    =
                                                                    let uu____80041
                                                                    =
                                                                    let uu____80042
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____80043
                                                                    =
                                                                    let uu____80054
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____80054)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____80042
                                                                    uu____80043
                                                                     in
                                                                    (uu____80041,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____80033
                                                                     in
                                                                    [uu____80032]
                                                                     in
                                                                    (d3,
                                                                    uu____80029)
                                                                     in
                                                                    match uu____80005
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____79956
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____80111
                                                                    =
                                                                    let uu____80114
                                                                    =
                                                                    let uu____80117
                                                                    =
                                                                    let uu____80120
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____80120
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____80117
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____80114
                                                                     in
                                                                    let uu____80127
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____80111,
                                                                    uu____80127,
                                                                    env02))))))))))
                                      in
                                   let uu____80132 =
                                     let uu____80145 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____80208  ->
                                          fun uu____80209  ->
                                            match (uu____80208, uu____80209)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____80334 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____80334 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____80145
                                      in
                                   (match uu____80132 with
                                    | (decls2,eqns,env01) ->
                                        let uu____80401 =
                                          let isDeclFun uu___640_80418 =
                                            match uu___640_80418 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____80420 -> true
                                            | uu____80433 -> false  in
                                          let uu____80435 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____80435
                                            (fun decls3  ->
                                               let uu____80465 =
                                                 FStar_List.fold_left
                                                   (fun uu____80496  ->
                                                      fun elt  ->
                                                        match uu____80496
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____80537 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____80537
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____80565
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____80565
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
                                                                    let uu___1459_80603
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_80603.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_80603.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_80603.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____80465 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____80635 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____80635, elts, rest))
                                           in
                                        (match uu____80401 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____80664 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_80670  ->
                                        match uu___641_80670 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____80673 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____80681 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____80681)))
                                in
                             if uu____80664
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_80703  ->
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
                   let uu____80742 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____80742
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____80761 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____80761, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____80817 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____80817 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____80823 = encode_sigelt' env se  in
      match uu____80823 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____80835 =
                  let uu____80838 =
                    let uu____80839 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____80839  in
                  [uu____80838]  in
                FStar_All.pipe_right uu____80835
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____80844 ->
                let uu____80845 =
                  let uu____80848 =
                    let uu____80851 =
                      let uu____80852 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____80852  in
                    [uu____80851]  in
                  FStar_All.pipe_right uu____80848
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____80859 =
                  let uu____80862 =
                    let uu____80865 =
                      let uu____80868 =
                        let uu____80869 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____80869  in
                      [uu____80868]  in
                    FStar_All.pipe_right uu____80865
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____80862  in
                FStar_List.append uu____80845 uu____80859
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____80883 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____80883
       then
         let uu____80888 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____80888
       else ());
      (let is_opaque_to_smt t =
         let uu____80900 =
           let uu____80901 = FStar_Syntax_Subst.compress t  in
           uu____80901.FStar_Syntax_Syntax.n  in
         match uu____80900 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80906)) -> s = "opaque_to_smt"
         | uu____80911 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____80920 =
           let uu____80921 = FStar_Syntax_Subst.compress t  in
           uu____80921.FStar_Syntax_Syntax.n  in
         match uu____80920 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____80926)) -> s = "uninterpreted_by_smt"
         | uu____80931 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____80937 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____80943 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____80955 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____80956 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____80957 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____80970 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____80972 =
             let uu____80974 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____80974  in
           if uu____80972
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____81003 ->
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
                let uu____81035 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____81035 with
                | (formals,uu____81055) ->
                    let arity = FStar_List.length formals  in
                    let uu____81079 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____81079 with
                     | (aname,atok,env2) ->
                         let uu____81101 =
                           let uu____81106 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____81106 env2
                            in
                         (match uu____81101 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____81118 =
                                  let uu____81119 =
                                    let uu____81131 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____81151  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____81131,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____81119
                                   in
                                [uu____81118;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____81168 =
                                let aux uu____81214 uu____81215 =
                                  match (uu____81214, uu____81215) with
                                  | ((bv,uu____81259),(env3,acc_sorts,acc))
                                      ->
                                      let uu____81291 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____81291 with
                                       | (xxsym,xx,env4) ->
                                           let uu____81314 =
                                             let uu____81317 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____81317 :: acc_sorts  in
                                           (env4, uu____81314, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____81168 with
                               | (uu____81349,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____81365 =
                                       let uu____81373 =
                                         let uu____81374 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____81375 =
                                           let uu____81386 =
                                             let uu____81387 =
                                               let uu____81392 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____81392)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____81387
                                              in
                                           ([[app]], xs_sorts, uu____81386)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____81374 uu____81375
                                          in
                                       (uu____81373,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____81365
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____81407 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____81407
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____81410 =
                                       let uu____81418 =
                                         let uu____81419 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____81420 =
                                           let uu____81431 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____81431)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____81419 uu____81420
                                          in
                                       (uu____81418,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____81410
                                      in
                                   let uu____81444 =
                                     let uu____81447 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____81447  in
                                   (env2, uu____81444))))
                 in
              let uu____81456 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____81456 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____81482,uu____81483)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____81484 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____81484 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____81506,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____81513 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_81519  ->
                       match uu___642_81519 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____81522 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____81528 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____81531 -> false))
                in
             Prims.op_Negation uu____81513  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____81541 =
                let uu____81546 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____81546 env fv t quals  in
              match uu____81541 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____81560 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____81560  in
                  let uu____81563 =
                    let uu____81564 =
                      let uu____81567 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____81567
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____81564  in
                  (uu____81563, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____81577 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____81577 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_81589 = env  in
                  let uu____81590 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_81589.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_81589.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_81589.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____81590;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_81589.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_81589.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_81589.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_81589.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_81589.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_81589.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_81589.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____81592 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____81592 with
                 | (f3,decls) ->
                     let g =
                       let uu____81606 =
                         let uu____81609 =
                           let uu____81610 =
                             let uu____81618 =
                               let uu____81619 =
                                 let uu____81621 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____81621
                                  in
                               FStar_Pervasives_Native.Some uu____81619  in
                             let uu____81625 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____81618, uu____81625)  in
                           FStar_SMTEncoding_Util.mkAssume uu____81610  in
                         [uu____81609]  in
                       FStar_All.pipe_right uu____81606
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____81634) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____81648 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____81670 =
                        let uu____81673 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____81673.FStar_Syntax_Syntax.fv_name  in
                      uu____81670.FStar_Syntax_Syntax.v  in
                    let uu____81674 =
                      let uu____81676 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____81676  in
                    if uu____81674
                    then
                      let val_decl =
                        let uu___1629_81708 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_81708.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_81708.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_81708.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____81709 = encode_sigelt' env1 val_decl  in
                      match uu____81709 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____81648 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____81745,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____81747;
                           FStar_Syntax_Syntax.lbtyp = uu____81748;
                           FStar_Syntax_Syntax.lbeff = uu____81749;
                           FStar_Syntax_Syntax.lbdef = uu____81750;
                           FStar_Syntax_Syntax.lbattrs = uu____81751;
                           FStar_Syntax_Syntax.lbpos = uu____81752;_}::[]),uu____81753)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____81772 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____81772 with
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
                  let uu____81810 =
                    let uu____81813 =
                      let uu____81814 =
                        let uu____81822 =
                          let uu____81823 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____81824 =
                            let uu____81835 =
                              let uu____81836 =
                                let uu____81841 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____81841)  in
                              FStar_SMTEncoding_Util.mkEq uu____81836  in
                            ([[b2t_x]], [xx], uu____81835)  in
                          FStar_SMTEncoding_Term.mkForall uu____81823
                            uu____81824
                           in
                        (uu____81822,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____81814  in
                    [uu____81813]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____81810
                   in
                let uu____81879 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____81879, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____81882,uu____81883) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_81893  ->
                   match uu___643_81893 with
                   | FStar_Syntax_Syntax.Discriminator uu____81895 -> true
                   | uu____81897 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____81899,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____81911 =
                      let uu____81913 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____81913.FStar_Ident.idText  in
                    uu____81911 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_81920  ->
                      match uu___644_81920 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____81923 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____81926) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_81940  ->
                   match uu___645_81940 with
                   | FStar_Syntax_Syntax.Projector uu____81942 -> true
                   | uu____81948 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____81952 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____81952 with
            | FStar_Pervasives_Native.Some uu____81959 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_81961 = se  in
                  let uu____81962 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____81962;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_81961.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_81961.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_81961.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____81965) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____81980) ->
           let uu____81989 = encode_sigelts env ses  in
           (match uu____81989 with
            | (g,env1) ->
                let uu____82000 =
                  FStar_List.fold_left
                    (fun uu____82024  ->
                       fun elt  ->
                         match uu____82024 with
                         | (g',inversions) ->
                             let uu____82052 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_82075  ->
                                       match uu___646_82075 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____82077;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____82078;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____82079;_}
                                           -> false
                                       | uu____82086 -> true))
                                in
                             (match uu____82052 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_82111 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_82111.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_82111.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_82111.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____82000 with
                 | (g',inversions) ->
                     let uu____82130 =
                       FStar_List.fold_left
                         (fun uu____82161  ->
                            fun elt  ->
                              match uu____82161 with
                              | (decls,elts,rest) ->
                                  let uu____82202 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_82211  ->
                                            match uu___647_82211 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____82213 -> true
                                            | uu____82226 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____82202
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____82249 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_82270  ->
                                               match uu___648_82270 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____82272 -> true
                                               | uu____82285 -> false))
                                        in
                                     match uu____82249 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_82316 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_82316.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_82316.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_82316.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____82130 with
                      | (decls,elts,rest) ->
                          let uu____82342 =
                            let uu____82343 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____82350 =
                              let uu____82353 =
                                let uu____82356 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____82356  in
                              FStar_List.append elts uu____82353  in
                            FStar_List.append uu____82343 uu____82350  in
                          (uu____82342, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____82367,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____82380 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____82380 with
             | (usubst,uvs) ->
                 let uu____82400 =
                   let uu____82407 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____82408 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____82409 =
                     let uu____82410 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____82410 k  in
                   (uu____82407, uu____82408, uu____82409)  in
                 (match uu____82400 with
                  | (env1,tps1,k1) ->
                      let uu____82423 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____82423 with
                       | (tps2,k2) ->
                           let uu____82431 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____82431 with
                            | (uu____82447,k3) ->
                                let uu____82469 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____82469 with
                                 | (tps3,env_tps,uu____82481,us) ->
                                     let u_k =
                                       let uu____82484 =
                                         let uu____82485 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____82486 =
                                           let uu____82491 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____82493 =
                                             let uu____82494 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____82494
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____82491 uu____82493
                                            in
                                         uu____82486
                                           FStar_Pervasives_Native.None
                                           uu____82485
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____82484 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____82512) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____82518,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____82521) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____82529,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____82536) ->
                                           let uu____82537 =
                                             let uu____82539 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____82539
                                              in
                                           failwith uu____82537
                                       | (uu____82543,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____82544 =
                                             let uu____82546 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____82546
                                              in
                                           failwith uu____82544
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____82550,uu____82551) ->
                                           let uu____82560 =
                                             let uu____82562 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____82562
                                              in
                                           failwith uu____82560
                                       | (uu____82566,FStar_Syntax_Syntax.U_unif
                                          uu____82567) ->
                                           let uu____82576 =
                                             let uu____82578 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____82578
                                              in
                                           failwith uu____82576
                                       | uu____82582 -> false  in
                                     let u_leq_u_k u =
                                       let uu____82595 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____82595 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____82613 = u_leq_u_k u_tp  in
                                       if uu____82613
                                       then true
                                       else
                                         (let uu____82620 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____82620 with
                                          | (formals,uu____82637) ->
                                              let uu____82658 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____82658 with
                                               | (uu____82668,uu____82669,uu____82670,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____82681 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____82681
             then
               let uu____82686 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____82686
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_82706  ->
                       match uu___649_82706 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____82710 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____82723 = c  in
                 match uu____82723 with
                 | (name,args,uu____82728,uu____82729,uu____82730) ->
                     let uu____82741 =
                       let uu____82742 =
                         let uu____82754 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____82781  ->
                                   match uu____82781 with
                                   | (uu____82790,sort,uu____82792) -> sort))
                            in
                         (name, uu____82754,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____82742  in
                     [uu____82741]
               else
                 (let uu____82803 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____82803 c)
                in
             let inversion_axioms tapp vars =
               let uu____82821 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____82829 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____82829 FStar_Option.isNone))
                  in
               if uu____82821
               then []
               else
                 (let uu____82864 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____82864 with
                  | (xxsym,xx) ->
                      let uu____82877 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____82916  ->
                                fun l  ->
                                  match uu____82916 with
                                  | (out,decls) ->
                                      let uu____82936 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____82936 with
                                       | (uu____82947,data_t) ->
                                           let uu____82949 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____82949 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____82993 =
                                                    let uu____82994 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____82994.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____82993 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____82997,indices)
                                                      -> indices
                                                  | uu____83023 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____83053  ->
                                                            match uu____83053
                                                            with
                                                            | (x,uu____83061)
                                                                ->
                                                                let uu____83066
                                                                  =
                                                                  let uu____83067
                                                                    =
                                                                    let uu____83075
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____83075,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____83067
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____83066)
                                                       env)
                                                   in
                                                let uu____83080 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____83080 with
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
                                                                  let uu____83115
                                                                    =
                                                                    let uu____83120
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____83120,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____83115)
                                                             vars indices1
                                                         else []  in
                                                       let uu____83123 =
                                                         let uu____83124 =
                                                           let uu____83129 =
                                                             let uu____83130
                                                               =
                                                               let uu____83135
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____83136
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____83135,
                                                                 uu____83136)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____83130
                                                              in
                                                           (out, uu____83129)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____83124
                                                          in
                                                       (uu____83123,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____82877 with
                       | (data_ax,decls) ->
                           let uu____83151 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____83151 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____83168 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____83168 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____83175 =
                                    let uu____83183 =
                                      let uu____83184 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____83185 =
                                        let uu____83196 =
                                          let uu____83197 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____83199 =
                                            let uu____83202 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____83202 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____83197 uu____83199
                                           in
                                        let uu____83204 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____83196,
                                          uu____83204)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____83184 uu____83185
                                       in
                                    let uu____83213 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____83183,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____83213)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____83175
                                   in
                                let uu____83219 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____83219)))
                in
             let uu____83226 =
               let uu____83231 =
                 let uu____83232 = FStar_Syntax_Subst.compress k  in
                 uu____83232.FStar_Syntax_Syntax.n  in
               match uu____83231 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____83267 -> (tps, k)  in
             match uu____83226 with
             | (formals,res) ->
                 let uu____83274 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____83274 with
                  | (formals1,res1) ->
                      let uu____83285 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____83285 with
                       | (vars,guards,env',binder_decls,uu____83310) ->
                           let arity = FStar_List.length vars  in
                           let uu____83324 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____83324 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____83350 =
                                    let uu____83358 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____83358)  in
                                  FStar_SMTEncoding_Util.mkApp uu____83350
                                   in
                                let uu____83364 =
                                  let tname_decl =
                                    let uu____83374 =
                                      let uu____83375 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____83394 =
                                                  let uu____83396 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____83396
                                                   in
                                                let uu____83398 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____83394, uu____83398,
                                                  false)))
                                         in
                                      let uu____83402 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____83375,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____83402, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____83374
                                     in
                                  let uu____83410 =
                                    match vars with
                                    | [] ->
                                        let uu____83423 =
                                          let uu____83424 =
                                            let uu____83427 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _83433  ->
                                                 FStar_Pervasives_Native.Some
                                                   _83433) uu____83427
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____83424
                                           in
                                        ([], uu____83423)
                                    | uu____83436 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____83446 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____83446
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____83462 =
                                            let uu____83470 =
                                              let uu____83471 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____83472 =
                                                let uu____83488 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____83488)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____83471 uu____83472
                                               in
                                            (uu____83470,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____83462
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____83410 with
                                  | (tok_decls,env2) ->
                                      let uu____83515 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____83515
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____83364 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____83543 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____83543 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____83565 =
                                                 let uu____83566 =
                                                   let uu____83574 =
                                                     let uu____83575 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____83575
                                                      in
                                                   (uu____83574,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____83566
                                                  in
                                               [uu____83565]
                                             else []  in
                                           let uu____83583 =
                                             let uu____83586 =
                                               let uu____83589 =
                                                 let uu____83592 =
                                                   let uu____83593 =
                                                     let uu____83601 =
                                                       let uu____83602 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____83603 =
                                                         let uu____83614 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____83614)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____83602
                                                         uu____83603
                                                        in
                                                     (uu____83601,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____83593
                                                    in
                                                 [uu____83592]  in
                                               FStar_List.append karr
                                                 uu____83589
                                                in
                                             FStar_All.pipe_right uu____83586
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____83583
                                        in
                                     let aux =
                                       let uu____83633 =
                                         let uu____83636 =
                                           inversion_axioms tapp vars  in
                                         let uu____83639 =
                                           let uu____83642 =
                                             let uu____83645 =
                                               let uu____83646 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____83646 env2
                                                 tapp vars
                                                in
                                             [uu____83645]  in
                                           FStar_All.pipe_right uu____83642
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____83636
                                           uu____83639
                                          in
                                       FStar_List.append kindingAx
                                         uu____83633
                                        in
                                     let g =
                                       let uu____83654 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____83654
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____83662,uu____83663,uu____83664,uu____83665,uu____83666)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____83674,t,uu____83676,n_tps,uu____83678) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____83688 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____83688 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____83736 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____83736 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____83760 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____83760 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____83780 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____83780 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____83859 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____83859,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____83866 =
                                   let uu____83867 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____83867, true)
                                    in
                                 let uu____83875 =
                                   let uu____83882 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____83882
                                    in
                                 FStar_All.pipe_right uu____83866 uu____83875
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
                               let uu____83894 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____83894 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____83906::uu____83907 ->
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
                                            let uu____83956 =
                                              let uu____83957 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____83957]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____83956
                                             in
                                          let uu____83983 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____83984 =
                                            let uu____83995 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____83995)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____83983 uu____83984
                                      | uu____84022 -> tok_typing  in
                                    let uu____84033 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____84033 with
                                     | (vars',guards',env'',decls_formals,uu____84058)
                                         ->
                                         let uu____84071 =
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
                                         (match uu____84071 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____84101 ->
                                                    let uu____84110 =
                                                      let uu____84111 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____84111
                                                       in
                                                    [uu____84110]
                                                 in
                                              let encode_elim uu____84127 =
                                                let uu____84128 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____84128 with
                                                | (head1,args) ->
                                                    let uu____84179 =
                                                      let uu____84180 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____84180.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____84179 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____84192;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____84193;_},uu____84194)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____84200 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84200
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
                                                                  | uu____84263
                                                                    ->
                                                                    let uu____84264
                                                                    =
                                                                    let uu____84270
                                                                    =
                                                                    let uu____84272
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84272
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84270)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84264
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84295
                                                                    =
                                                                    let uu____84297
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84297
                                                                     in
                                                                    if
                                                                    uu____84295
                                                                    then
                                                                    let uu____84319
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84319]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84322
                                                                =
                                                                let uu____84336
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____84393
                                                                     ->
                                                                    fun
                                                                    uu____84394
                                                                     ->
                                                                    match 
                                                                    (uu____84393,
                                                                    uu____84394)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____84505
                                                                    =
                                                                    let uu____84513
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____84513
                                                                     in
                                                                    (match uu____84505
                                                                    with
                                                                    | 
                                                                    (uu____84527,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____84538
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____84538
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____84543
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____84543
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
                                                                  uu____84336
                                                                 in
                                                              (match uu____84322
                                                               with
                                                               | (uu____84564,arg_vars,elim_eqns_or_guards,uu____84567)
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
                                                                    let uu____84594
                                                                    =
                                                                    let uu____84602
                                                                    =
                                                                    let uu____84603
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84604
                                                                    =
                                                                    let uu____84615
                                                                    =
                                                                    let uu____84616
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____84616
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84618
                                                                    =
                                                                    let uu____84619
                                                                    =
                                                                    let uu____84624
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____84624)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84619
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84615,
                                                                    uu____84618)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84603
                                                                    uu____84604
                                                                     in
                                                                    (uu____84602,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84594
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____84639
                                                                    =
                                                                    let uu____84640
                                                                    =
                                                                    let uu____84646
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____84646,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84640
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84639
                                                                     in
                                                                    let uu____84649
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____84649
                                                                    then
                                                                    let x =
                                                                    let uu____84653
                                                                    =
                                                                    let uu____84659
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____84659,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____84653
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____84664
                                                                    =
                                                                    let uu____84672
                                                                    =
                                                                    let uu____84673
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____84674
                                                                    =
                                                                    let uu____84685
                                                                    =
                                                                    let uu____84690
                                                                    =
                                                                    let uu____84693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____84693]
                                                                     in
                                                                    [uu____84690]
                                                                     in
                                                                    let uu____84698
                                                                    =
                                                                    let uu____84699
                                                                    =
                                                                    let uu____84704
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____84706
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____84704,
                                                                    uu____84706)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84699
                                                                     in
                                                                    (uu____84685,
                                                                    [x],
                                                                    uu____84698)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84673
                                                                    uu____84674
                                                                     in
                                                                    let uu____84727
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____84672,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____84727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84664
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____84738
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
                                                                    (let uu____84761
                                                                    =
                                                                    let uu____84762
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____84762
                                                                    dapp1  in
                                                                    [uu____84761])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____84738
                                                                    FStar_List.flatten
                                                                     in
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
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____84793
                                                                    =
                                                                    let uu____84794
                                                                    =
                                                                    let uu____84799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____84799)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84794
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____84790,
                                                                    uu____84793)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84778
                                                                    uu____84779
                                                                     in
                                                                    (uu____84777,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84769)
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
                                                         let uu____84818 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____84818
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
                                                                  | uu____84881
                                                                    ->
                                                                    let uu____84882
                                                                    =
                                                                    let uu____84888
                                                                    =
                                                                    let uu____84890
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____84890
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____84888)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____84882
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____84913
                                                                    =
                                                                    let uu____84915
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____84915
                                                                     in
                                                                    if
                                                                    uu____84913
                                                                    then
                                                                    let uu____84937
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____84937]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____84940
                                                                =
                                                                let uu____84954
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____85011
                                                                     ->
                                                                    fun
                                                                    uu____85012
                                                                     ->
                                                                    match 
                                                                    (uu____85011,
                                                                    uu____85012)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____85123
                                                                    =
                                                                    let uu____85131
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____85131
                                                                     in
                                                                    (match uu____85123
                                                                    with
                                                                    | 
                                                                    (uu____85145,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____85156
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____85156
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____85161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____85161
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
                                                                  uu____84954
                                                                 in
                                                              (match uu____84940
                                                               with
                                                               | (uu____85182,arg_vars,elim_eqns_or_guards,uu____85185)
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
                                                                    let uu____85212
                                                                    =
                                                                    let uu____85220
                                                                    =
                                                                    let uu____85221
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____85222
                                                                    =
                                                                    let uu____85233
                                                                    =
                                                                    let uu____85234
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____85234
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____85236
                                                                    =
                                                                    let uu____85237
                                                                    =
                                                                    let uu____85242
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____85242)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____85237
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____85233,
                                                                    uu____85236)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____85221
                                                                    uu____85222
                                                                     in
                                                                    (uu____85220,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____85212
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____85257
                                                                    =
                                                                    let uu____85258
                                                                    =
                                                                    let uu____85264
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____85264,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____85258
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____85257
                                                                     in
                                                                    let uu____85267
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____85267
                                                                    then
                                                                    let x =
                                                                    let uu____85271
                                                                    =
                                                                    let uu____85277
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____85277,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____85271
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____85282
                                                                    =
                                                                    let uu____85290
                                                                    =
                                                                    let uu____85291
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____85292
                                                                    =
                                                                    let uu____85303
                                                                    =
                                                                    let uu____85308
                                                                    =
                                                                    let uu____85311
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____85311]
                                                                     in
                                                                    [uu____85308]
                                                                     in
                                                                    let uu____85316
                                                                    =
                                                                    let uu____85317
                                                                    =
                                                                    let uu____85322
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____85324
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____85322,
                                                                    uu____85324)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____85317
                                                                     in
                                                                    (uu____85303,
                                                                    [x],
                                                                    uu____85316)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____85291
                                                                    uu____85292
                                                                     in
                                                                    let uu____85345
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____85290,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____85345)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____85282
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____85356
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
                                                                    (let uu____85379
                                                                    =
                                                                    let uu____85380
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____85380
                                                                    dapp1  in
                                                                    [uu____85379])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____85356
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____85387
                                                                    =
                                                                    let uu____85395
                                                                    =
                                                                    let uu____85396
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____85397
                                                                    =
                                                                    let uu____85408
                                                                    =
                                                                    let uu____85409
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____85409
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____85411
                                                                    =
                                                                    let uu____85412
                                                                    =
                                                                    let uu____85417
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____85417)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____85412
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____85408,
                                                                    uu____85411)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____85396
                                                                    uu____85397
                                                                     in
                                                                    (uu____85395,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____85387)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____85434 ->
                                                         ((let uu____85436 =
                                                             let uu____85442
                                                               =
                                                               let uu____85444
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____85446
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____85444
                                                                 uu____85446
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____85442)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____85436);
                                                          ([], [])))
                                                 in
                                              let uu____85454 =
                                                encode_elim ()  in
                                              (match uu____85454 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____85480 =
                                                       let uu____85483 =
                                                         let uu____85486 =
                                                           let uu____85489 =
                                                             let uu____85492
                                                               =
                                                               let uu____85495
                                                                 =
                                                                 let uu____85498
                                                                   =
                                                                   let uu____85499
                                                                    =
                                                                    let uu____85511
                                                                    =
                                                                    let uu____85512
                                                                    =
                                                                    let uu____85514
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____85514
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____85512
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____85511)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____85499
                                                                    in
                                                                 [uu____85498]
                                                                  in
                                                               FStar_List.append
                                                                 uu____85495
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____85492
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____85525 =
                                                             let uu____85528
                                                               =
                                                               let uu____85531
                                                                 =
                                                                 let uu____85534
                                                                   =
                                                                   let uu____85537
                                                                    =
                                                                    let uu____85540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____85545
                                                                    =
                                                                    let uu____85548
                                                                    =
                                                                    let uu____85549
                                                                    =
                                                                    let uu____85557
                                                                    =
                                                                    let uu____85558
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____85559
                                                                    =
                                                                    let uu____85570
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____85570)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____85558
                                                                    uu____85559
                                                                     in
                                                                    (uu____85557,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____85549
                                                                     in
                                                                    let uu____85583
                                                                    =
                                                                    let uu____85586
                                                                    =
                                                                    let uu____85587
                                                                    =
                                                                    let uu____85595
                                                                    =
                                                                    let uu____85596
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____85597
                                                                    =
                                                                    let uu____85608
                                                                    =
                                                                    let uu____85609
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____85609
                                                                    vars'  in
                                                                    let uu____85611
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____85608,
                                                                    uu____85611)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____85596
                                                                    uu____85597
                                                                     in
                                                                    (uu____85595,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____85587
                                                                     in
                                                                    [uu____85586]
                                                                     in
                                                                    uu____85548
                                                                    ::
                                                                    uu____85583
                                                                     in
                                                                    uu____85540
                                                                    ::
                                                                    uu____85545
                                                                     in
                                                                   FStar_List.append
                                                                    uu____85537
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____85534
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____85531
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____85528
                                                              in
                                                           FStar_List.append
                                                             uu____85489
                                                             uu____85525
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____85486
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____85483
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____85480
                                                      in
                                                   let uu____85628 =
                                                     let uu____85629 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____85629 g
                                                      in
                                                   (uu____85628, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____85663  ->
              fun se  ->
                match uu____85663 with
                | (g,env1) ->
                    let uu____85683 = encode_sigelt env1 se  in
                    (match uu____85683 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____85751 =
        match uu____85751 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____85788 ->
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
                 ((let uu____85796 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____85796
                   then
                     let uu____85801 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____85803 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____85805 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____85801 uu____85803 uu____85805
                   else ());
                  (let uu____85810 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____85810 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____85828 =
                         let uu____85836 =
                           let uu____85838 =
                             let uu____85840 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____85840
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____85838  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____85836
                          in
                       (match uu____85828 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____85860 = FStar_Options.log_queries ()
                                 in
                              if uu____85860
                              then
                                let uu____85863 =
                                  let uu____85865 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____85867 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____85869 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____85865 uu____85867 uu____85869
                                   in
                                FStar_Pervasives_Native.Some uu____85863
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____85885 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____85895 =
                                let uu____85898 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____85898  in
                              FStar_List.append uu____85885 uu____85895  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____85910,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____85930 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____85930 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____85951 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____85951 with | (uu____85978,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____86031  ->
              match uu____86031 with
              | (l,uu____86040,uu____86041) ->
                  let uu____86044 =
                    let uu____86056 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____86056, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____86044))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____86089  ->
              match uu____86089 with
              | (l,uu____86100,uu____86101) ->
                  let uu____86104 =
                    let uu____86105 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _86108  -> FStar_SMTEncoding_Term.Echo _86108)
                      uu____86105
                     in
                  let uu____86109 =
                    let uu____86112 =
                      let uu____86113 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____86113  in
                    [uu____86112]  in
                  uu____86104 :: uu____86109))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____86131 =
      let uu____86134 =
        let uu____86135 = FStar_Util.psmap_empty ()  in
        let uu____86150 =
          let uu____86159 = FStar_Util.psmap_empty ()  in (uu____86159, [])
           in
        let uu____86166 =
          let uu____86168 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____86168 FStar_Ident.string_of_lid  in
        let uu____86170 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____86135;
          FStar_SMTEncoding_Env.fvar_bindings = uu____86150;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____86166;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____86170
        }  in
      [uu____86134]  in
    FStar_ST.op_Colon_Equals last_env uu____86131
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____86214 = FStar_ST.op_Bang last_env  in
      match uu____86214 with
      | [] -> failwith "No env; call init first!"
      | e::uu____86242 ->
          let uu___2175_86245 = e  in
          let uu____86246 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_86245.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_86245.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_86245.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_86245.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_86245.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_86245.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_86245.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____86246;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_86245.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_86245.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____86254 = FStar_ST.op_Bang last_env  in
    match uu____86254 with
    | [] -> failwith "Empty env stack"
    | uu____86281::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____86313  ->
    let uu____86314 = FStar_ST.op_Bang last_env  in
    match uu____86314 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____86374  ->
    let uu____86375 = FStar_ST.op_Bang last_env  in
    match uu____86375 with
    | [] -> failwith "Popping an empty stack"
    | uu____86402::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____86439  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____86492  ->
         let uu____86493 = snapshot_env ()  in
         match uu____86493 with
         | (env_depth,()) ->
             let uu____86515 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____86515 with
              | (varops_depth,()) ->
                  let uu____86537 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____86537 with
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
        (fun uu____86595  ->
           let uu____86596 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____86596 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____86691 = snapshot msg  in () 
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
        | (uu____86737::uu____86738,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_86746 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_86746.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_86746.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_86746.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____86747 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_86774 = elt  in
        let uu____86775 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_86774.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_86774.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____86775;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_86774.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____86795 =
        let uu____86798 =
          let uu____86799 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____86799  in
        let uu____86800 = open_fact_db_tags env  in uu____86798 ::
          uu____86800
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____86795
  
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
      let uu____86827 = encode_sigelt env se  in
      match uu____86827 with
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
                (let uu____86873 =
                   let uu____86876 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____86876
                    in
                 match uu____86873 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____86891 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____86891
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____86921 = FStar_Options.log_queries ()  in
        if uu____86921
        then
          let uu____86926 =
            let uu____86927 =
              let uu____86929 =
                let uu____86931 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____86931 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____86929  in
            FStar_SMTEncoding_Term.Caption uu____86927  in
          uu____86926 :: decls
        else decls  in
      (let uu____86950 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____86950
       then
         let uu____86953 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____86953
       else ());
      (let env =
         let uu____86959 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____86959 tcenv  in
       let uu____86960 = encode_top_level_facts env se  in
       match uu____86960 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____86974 =
               let uu____86977 =
                 let uu____86980 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____86980
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____86977  in
             FStar_SMTEncoding_Z3.giveZ3 uu____86974)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____87013 = FStar_Options.log_queries ()  in
          if uu____87013
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_87033 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_87033.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_87033.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_87033.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_87033.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_87033.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_87033.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_87033.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_87033.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_87033.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_87033.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____87038 =
             let uu____87041 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____87041
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____87038  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____87061 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____87061
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
          (let uu____87085 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____87085
           then
             let uu____87088 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____87088
           else ());
          (let env =
             let uu____87096 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____87096
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____87135  ->
                     fun se  ->
                       match uu____87135 with
                       | (g,env2) ->
                           let uu____87155 = encode_top_level_facts env2 se
                              in
                           (match uu____87155 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____87178 =
             encode_signature
               (let uu___2303_87187 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_87187.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_87187.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_87187.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_87187.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_87187.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_87187.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_87187.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_87187.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_87187.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_87187.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____87178 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____87203 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____87203
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____87209 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____87209))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____87237  ->
        match uu____87237 with
        | (decls,fvbs) ->
            ((let uu____87251 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____87251
              then ()
              else
                (let uu____87256 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____87256
                 then
                   let uu____87259 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____87259
                 else ()));
             (let env =
                let uu____87267 = get_env name tcenv  in
                FStar_All.pipe_right uu____87267
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____87269 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____87269
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____87283 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____87283
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
        (let uu____87345 =
           let uu____87347 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____87347.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____87345);
        (let env =
           let uu____87349 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____87349 tcenv  in
         let uu____87350 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____87389 = aux rest  in
                 (match uu____87389 with
                  | (out,rest1) ->
                      let t =
                        let uu____87417 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____87417 with
                        | FStar_Pervasives_Native.Some uu____87420 ->
                            let uu____87421 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____87421
                              x.FStar_Syntax_Syntax.sort
                        | uu____87422 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____87426 =
                        let uu____87429 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_87432 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_87432.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_87432.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____87429 :: out  in
                      (uu____87426, rest1))
             | uu____87437 -> ([], bindings)  in
           let uu____87444 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____87444 with
           | (closing,bindings) ->
               let uu____87471 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____87471, bindings)
            in
         match uu____87350 with
         | (q1,bindings) ->
             let uu____87502 = encode_env_bindings env bindings  in
             (match uu____87502 with
              | (env_decls,env1) ->
                  ((let uu____87524 =
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
                    if uu____87524
                    then
                      let uu____87531 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____87531
                    else ());
                   (let uu____87536 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____87536 with
                    | (phi,qdecls) ->
                        let uu____87557 =
                          let uu____87562 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____87562 phi
                           in
                        (match uu____87557 with
                         | (labels,phi1) ->
                             let uu____87579 = encode_labels labels  in
                             (match uu____87579 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____87615 =
                                      FStar_Options.log_queries ()  in
                                    if uu____87615
                                    then
                                      let uu____87620 =
                                        let uu____87621 =
                                          let uu____87623 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____87623
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____87621
                                         in
                                      [uu____87620]
                                    else []  in
                                  let query_prelude =
                                    let uu____87631 =
                                      let uu____87632 =
                                        let uu____87633 =
                                          let uu____87636 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____87643 =
                                            let uu____87646 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____87646
                                             in
                                          FStar_List.append uu____87636
                                            uu____87643
                                           in
                                        FStar_List.append env_decls
                                          uu____87633
                                         in
                                      FStar_All.pipe_right uu____87632
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____87631
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____87656 =
                                      let uu____87664 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____87665 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____87664,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____87665)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____87656
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
  