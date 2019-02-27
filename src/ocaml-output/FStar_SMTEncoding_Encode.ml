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
  let uu____72843 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72843 with
  | (asym,a) ->
      let uu____72854 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72854 with
       | (xsym,x) ->
           let uu____72865 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72865 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72943 =
                      let uu____72955 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72955, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72943  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72975 =
                      let uu____72983 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72983)  in
                    FStar_SMTEncoding_Util.mkApp uu____72975  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____73002 =
                    let uu____73005 =
                      let uu____73008 =
                        let uu____73011 =
                          let uu____73012 =
                            let uu____73020 =
                              let uu____73021 =
                                let uu____73032 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____73032)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____73021
                               in
                            (uu____73020, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____73012  in
                        let uu____73044 =
                          let uu____73047 =
                            let uu____73048 =
                              let uu____73056 =
                                let uu____73057 =
                                  let uu____73068 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____73068)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____73057
                                 in
                              (uu____73056,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____73048  in
                          [uu____73047]  in
                        uu____73011 :: uu____73044  in
                      xtok_decl :: uu____73008  in
                    xname_decl :: uu____73005  in
                  (xtok1, (FStar_List.length vars), uu____73002)  in
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
                  let uu____73238 =
                    let uu____73259 =
                      let uu____73278 =
                        let uu____73279 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73279
                         in
                      quant axy uu____73278  in
                    (FStar_Parser_Const.op_Eq, uu____73259)  in
                  let uu____73296 =
                    let uu____73319 =
                      let uu____73340 =
                        let uu____73359 =
                          let uu____73360 =
                            let uu____73361 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73361  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73360
                           in
                        quant axy uu____73359  in
                      (FStar_Parser_Const.op_notEq, uu____73340)  in
                    let uu____73378 =
                      let uu____73401 =
                        let uu____73422 =
                          let uu____73441 =
                            let uu____73442 =
                              let uu____73443 =
                                let uu____73448 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73449 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73448, uu____73449)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73443  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73442
                             in
                          quant xy uu____73441  in
                        (FStar_Parser_Const.op_And, uu____73422)  in
                      let uu____73466 =
                        let uu____73489 =
                          let uu____73510 =
                            let uu____73529 =
                              let uu____73530 =
                                let uu____73531 =
                                  let uu____73536 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73537 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73536, uu____73537)  in
                                FStar_SMTEncoding_Util.mkOr uu____73531  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73530
                               in
                            quant xy uu____73529  in
                          (FStar_Parser_Const.op_Or, uu____73510)  in
                        let uu____73554 =
                          let uu____73577 =
                            let uu____73598 =
                              let uu____73617 =
                                let uu____73618 =
                                  let uu____73619 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73619
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73618
                                 in
                              quant qx uu____73617  in
                            (FStar_Parser_Const.op_Negation, uu____73598)  in
                          let uu____73636 =
                            let uu____73659 =
                              let uu____73680 =
                                let uu____73699 =
                                  let uu____73700 =
                                    let uu____73701 =
                                      let uu____73706 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73707 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73706, uu____73707)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73701
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73700
                                   in
                                quant xy uu____73699  in
                              (FStar_Parser_Const.op_LT, uu____73680)  in
                            let uu____73724 =
                              let uu____73747 =
                                let uu____73768 =
                                  let uu____73787 =
                                    let uu____73788 =
                                      let uu____73789 =
                                        let uu____73794 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73795 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73794, uu____73795)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73789
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73788
                                     in
                                  quant xy uu____73787  in
                                (FStar_Parser_Const.op_LTE, uu____73768)  in
                              let uu____73812 =
                                let uu____73835 =
                                  let uu____73856 =
                                    let uu____73875 =
                                      let uu____73876 =
                                        let uu____73877 =
                                          let uu____73882 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73883 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73882, uu____73883)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73877
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73876
                                       in
                                    quant xy uu____73875  in
                                  (FStar_Parser_Const.op_GT, uu____73856)  in
                                let uu____73900 =
                                  let uu____73923 =
                                    let uu____73944 =
                                      let uu____73963 =
                                        let uu____73964 =
                                          let uu____73965 =
                                            let uu____73970 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73971 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73970, uu____73971)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73965
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73964
                                         in
                                      quant xy uu____73963  in
                                    (FStar_Parser_Const.op_GTE, uu____73944)
                                     in
                                  let uu____73988 =
                                    let uu____74011 =
                                      let uu____74032 =
                                        let uu____74051 =
                                          let uu____74052 =
                                            let uu____74053 =
                                              let uu____74058 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____74059 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____74058, uu____74059)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____74053
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____74052
                                           in
                                        quant xy uu____74051  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____74032)
                                       in
                                    let uu____74076 =
                                      let uu____74099 =
                                        let uu____74120 =
                                          let uu____74139 =
                                            let uu____74140 =
                                              let uu____74141 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74141
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74140
                                             in
                                          quant qx uu____74139  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74120)
                                         in
                                      let uu____74158 =
                                        let uu____74181 =
                                          let uu____74202 =
                                            let uu____74221 =
                                              let uu____74222 =
                                                let uu____74223 =
                                                  let uu____74228 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74229 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74228, uu____74229)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74223
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74222
                                               in
                                            quant xy uu____74221  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74202)
                                           in
                                        let uu____74246 =
                                          let uu____74269 =
                                            let uu____74290 =
                                              let uu____74309 =
                                                let uu____74310 =
                                                  let uu____74311 =
                                                    let uu____74316 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74317 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74316,
                                                      uu____74317)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74311
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74310
                                                 in
                                              quant xy uu____74309  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74290)
                                             in
                                          let uu____74334 =
                                            let uu____74357 =
                                              let uu____74378 =
                                                let uu____74397 =
                                                  let uu____74398 =
                                                    let uu____74399 =
                                                      let uu____74404 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74405 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74404,
                                                        uu____74405)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74399
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74398
                                                   in
                                                quant xy uu____74397  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74378)
                                               in
                                            let uu____74422 =
                                              let uu____74445 =
                                                let uu____74466 =
                                                  let uu____74485 =
                                                    let uu____74486 =
                                                      let uu____74487 =
                                                        let uu____74492 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74493 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74492,
                                                          uu____74493)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74487
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74486
                                                     in
                                                  quant xy uu____74485  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74466)
                                                 in
                                              let uu____74510 =
                                                let uu____74533 =
                                                  let uu____74554 =
                                                    let uu____74573 =
                                                      let uu____74574 =
                                                        let uu____74575 =
                                                          let uu____74580 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74581 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74580,
                                                            uu____74581)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74575
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74574
                                                       in
                                                    quant xy uu____74573  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74554)
                                                   in
                                                let uu____74598 =
                                                  let uu____74621 =
                                                    let uu____74642 =
                                                      let uu____74661 =
                                                        let uu____74662 =
                                                          let uu____74663 =
                                                            let uu____74668 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74669 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74668,
                                                              uu____74669)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74663
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74662
                                                         in
                                                      quant xy uu____74661
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74642)
                                                     in
                                                  let uu____74686 =
                                                    let uu____74709 =
                                                      let uu____74730 =
                                                        let uu____74749 =
                                                          let uu____74750 =
                                                            let uu____74751 =
                                                              let uu____74756
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74757
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74756,
                                                                uu____74757)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74751
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74750
                                                           in
                                                        quant xy uu____74749
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74730)
                                                       in
                                                    let uu____74774 =
                                                      let uu____74797 =
                                                        let uu____74818 =
                                                          let uu____74837 =
                                                            let uu____74838 =
                                                              let uu____74839
                                                                =
                                                                let uu____74844
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74845
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74844,
                                                                  uu____74845)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74839
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74838
                                                             in
                                                          quant xy
                                                            uu____74837
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74818)
                                                         in
                                                      let uu____74862 =
                                                        let uu____74885 =
                                                          let uu____74906 =
                                                            let uu____74925 =
                                                              let uu____74926
                                                                =
                                                                let uu____74927
                                                                  =
                                                                  let uu____74932
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74933
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74932,
                                                                    uu____74933)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74927
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74926
                                                               in
                                                            quant xy
                                                              uu____74925
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74906)
                                                           in
                                                        let uu____74950 =
                                                          let uu____74973 =
                                                            let uu____74994 =
                                                              let uu____75013
                                                                =
                                                                let uu____75014
                                                                  =
                                                                  let uu____75015
                                                                    =
                                                                    let uu____75020
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75021
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75020,
                                                                    uu____75021)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____75015
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____75014
                                                                 in
                                                              quant xy
                                                                uu____75013
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74994)
                                                             in
                                                          let uu____75038 =
                                                            let uu____75061 =
                                                              let uu____75082
                                                                =
                                                                let uu____75101
                                                                  =
                                                                  let uu____75102
                                                                    =
                                                                    let uu____75103
                                                                    =
                                                                    let uu____75108
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75109
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75108,
                                                                    uu____75109)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75103
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75102
                                                                   in
                                                                quant xy
                                                                  uu____75101
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75082)
                                                               in
                                                            let uu____75126 =
                                                              let uu____75149
                                                                =
                                                                let uu____75170
                                                                  =
                                                                  let uu____75189
                                                                    =
                                                                    let uu____75190
                                                                    =
                                                                    let uu____75191
                                                                    =
                                                                    let uu____75196
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75197
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75196,
                                                                    uu____75197)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75191
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75190
                                                                     in
                                                                  quant xy
                                                                    uu____75189
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75170)
                                                                 in
                                                              let uu____75214
                                                                =
                                                                let uu____75237
                                                                  =
                                                                  let uu____75258
                                                                    =
                                                                    let uu____75277
                                                                    =
                                                                    let uu____75278
                                                                    =
                                                                    let uu____75279
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75279
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75278
                                                                     in
                                                                    quant qx
                                                                    uu____75277
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75258)
                                                                   in
                                                                [uu____75237]
                                                                 in
                                                              uu____75149 ::
                                                                uu____75214
                                                               in
                                                            uu____75061 ::
                                                              uu____75126
                                                             in
                                                          uu____74973 ::
                                                            uu____75038
                                                           in
                                                        uu____74885 ::
                                                          uu____74950
                                                         in
                                                      uu____74797 ::
                                                        uu____74862
                                                       in
                                                    uu____74709 ::
                                                      uu____74774
                                                     in
                                                  uu____74621 :: uu____74686
                                                   in
                                                uu____74533 :: uu____74598
                                                 in
                                              uu____74445 :: uu____74510  in
                                            uu____74357 :: uu____74422  in
                                          uu____74269 :: uu____74334  in
                                        uu____74181 :: uu____74246  in
                                      uu____74099 :: uu____74158  in
                                    uu____74011 :: uu____74076  in
                                  uu____73923 :: uu____73988  in
                                uu____73835 :: uu____73900  in
                              uu____73747 :: uu____73812  in
                            uu____73659 :: uu____73724  in
                          uu____73577 :: uu____73636  in
                        uu____73489 :: uu____73554  in
                      uu____73401 :: uu____73466  in
                    uu____73319 :: uu____73378  in
                  uu____73238 :: uu____73296  in
                let mk1 l v1 =
                  let uu____75818 =
                    let uu____75830 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75920  ->
                              match uu____75920 with
                              | (l',uu____75941) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75830
                      (FStar_Option.map
                         (fun uu____76040  ->
                            match uu____76040 with
                            | (uu____76068,b) ->
                                let uu____76102 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76102 v1))
                     in
                  FStar_All.pipe_right uu____75818 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76185  ->
                          match uu____76185 with
                          | (l',uu____76206) -> FStar_Ident.lid_equals l l'))
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
          let uu____76280 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76280 with
          | (xxsym,xx) ->
              let uu____76291 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76291 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76307 =
                     let uu____76315 =
                       let uu____76316 =
                         let uu____76327 =
                           let uu____76328 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76338 =
                             let uu____76349 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76349 :: vars  in
                           uu____76328 :: uu____76338  in
                         let uu____76375 =
                           let uu____76376 =
                             let uu____76381 =
                               let uu____76382 =
                                 let uu____76387 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76387)  in
                               FStar_SMTEncoding_Util.mkEq uu____76382  in
                             (xx_has_type, uu____76381)  in
                           FStar_SMTEncoding_Util.mkImp uu____76376  in
                         ([[xx_has_type]], uu____76327, uu____76375)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76316  in
                     let uu____76400 =
                       let uu____76402 =
                         let uu____76404 =
                           let uu____76406 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76406  in
                         Prims.op_Hat module_name uu____76404  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76402
                        in
                     (uu____76315,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76400)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76307)
  
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
    let uu____76462 =
      let uu____76464 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76464  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76462  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76486 =
      let uu____76487 =
        let uu____76495 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76495, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76487  in
    let uu____76500 =
      let uu____76503 =
        let uu____76504 =
          let uu____76512 =
            let uu____76513 =
              let uu____76524 =
                let uu____76525 =
                  let uu____76530 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76530)  in
                FStar_SMTEncoding_Util.mkImp uu____76525  in
              ([[typing_pred]], [xx], uu____76524)  in
            let uu____76555 =
              let uu____76570 = FStar_TypeChecker_Env.get_range env  in
              let uu____76571 = mkForall_fuel1 env  in
              uu____76571 uu____76570  in
            uu____76555 uu____76513  in
          (uu____76512, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76504  in
      [uu____76503]  in
    uu____76486 :: uu____76500  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76618 =
      let uu____76619 =
        let uu____76627 =
          let uu____76628 = FStar_TypeChecker_Env.get_range env  in
          let uu____76629 =
            let uu____76640 =
              let uu____76645 =
                let uu____76648 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76648]  in
              [uu____76645]  in
            let uu____76653 =
              let uu____76654 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76654 tt  in
            (uu____76640, [bb], uu____76653)  in
          FStar_SMTEncoding_Term.mkForall uu____76628 uu____76629  in
        (uu____76627, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76619  in
    let uu____76679 =
      let uu____76682 =
        let uu____76683 =
          let uu____76691 =
            let uu____76692 =
              let uu____76703 =
                let uu____76704 =
                  let uu____76709 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76709)  in
                FStar_SMTEncoding_Util.mkImp uu____76704  in
              ([[typing_pred]], [xx], uu____76703)  in
            let uu____76736 =
              let uu____76751 = FStar_TypeChecker_Env.get_range env  in
              let uu____76752 = mkForall_fuel1 env  in
              uu____76752 uu____76751  in
            uu____76736 uu____76692  in
          (uu____76691, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76683  in
      [uu____76682]  in
    uu____76618 :: uu____76679  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76795 =
        let uu____76796 =
          let uu____76802 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76802, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76796  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76795  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76816 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76816  in
    let uu____76821 =
      let uu____76822 =
        let uu____76830 =
          let uu____76831 = FStar_TypeChecker_Env.get_range env  in
          let uu____76832 =
            let uu____76843 =
              let uu____76848 =
                let uu____76851 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76851]  in
              [uu____76848]  in
            let uu____76856 =
              let uu____76857 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76857 tt  in
            (uu____76843, [bb], uu____76856)  in
          FStar_SMTEncoding_Term.mkForall uu____76831 uu____76832  in
        (uu____76830, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76822  in
    let uu____76882 =
      let uu____76885 =
        let uu____76886 =
          let uu____76894 =
            let uu____76895 =
              let uu____76906 =
                let uu____76907 =
                  let uu____76912 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76912)  in
                FStar_SMTEncoding_Util.mkImp uu____76907  in
              ([[typing_pred]], [xx], uu____76906)  in
            let uu____76939 =
              let uu____76954 = FStar_TypeChecker_Env.get_range env  in
              let uu____76955 = mkForall_fuel1 env  in
              uu____76955 uu____76954  in
            uu____76939 uu____76895  in
          (uu____76894, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76886  in
      let uu____76977 =
        let uu____76980 =
          let uu____76981 =
            let uu____76989 =
              let uu____76990 =
                let uu____77001 =
                  let uu____77002 =
                    let uu____77007 =
                      let uu____77008 =
                        let uu____77011 =
                          let uu____77014 =
                            let uu____77017 =
                              let uu____77018 =
                                let uu____77023 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____77024 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____77023, uu____77024)  in
                              FStar_SMTEncoding_Util.mkGT uu____77018  in
                            let uu____77026 =
                              let uu____77029 =
                                let uu____77030 =
                                  let uu____77035 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____77036 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____77035, uu____77036)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77030  in
                              let uu____77038 =
                                let uu____77041 =
                                  let uu____77042 =
                                    let uu____77047 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____77048 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____77047, uu____77048)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77042  in
                                [uu____77041]  in
                              uu____77029 :: uu____77038  in
                            uu____77017 :: uu____77026  in
                          typing_pred_y :: uu____77014  in
                        typing_pred :: uu____77011  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77008  in
                    (uu____77007, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77002  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77001)
                 in
              let uu____77081 =
                let uu____77096 = FStar_TypeChecker_Env.get_range env  in
                let uu____77097 = mkForall_fuel1 env  in
                uu____77097 uu____77096  in
              uu____77081 uu____76990  in
            (uu____76989,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76981  in
        [uu____76980]  in
      uu____76885 :: uu____76977  in
    uu____76821 :: uu____76882  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77140 =
        let uu____77141 =
          let uu____77147 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77147, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77141  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77140  in
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
      let uu____77163 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77163  in
    let uu____77168 =
      let uu____77169 =
        let uu____77177 =
          let uu____77178 = FStar_TypeChecker_Env.get_range env  in
          let uu____77179 =
            let uu____77190 =
              let uu____77195 =
                let uu____77198 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77198]  in
              [uu____77195]  in
            let uu____77203 =
              let uu____77204 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77204 tt  in
            (uu____77190, [bb], uu____77203)  in
          FStar_SMTEncoding_Term.mkForall uu____77178 uu____77179  in
        (uu____77177, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77169  in
    let uu____77229 =
      let uu____77232 =
        let uu____77233 =
          let uu____77241 =
            let uu____77242 =
              let uu____77253 =
                let uu____77254 =
                  let uu____77259 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77259)  in
                FStar_SMTEncoding_Util.mkImp uu____77254  in
              ([[typing_pred]], [xx], uu____77253)  in
            let uu____77286 =
              let uu____77301 = FStar_TypeChecker_Env.get_range env  in
              let uu____77302 = mkForall_fuel1 env  in
              uu____77302 uu____77301  in
            uu____77286 uu____77242  in
          (uu____77241, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77233  in
      let uu____77324 =
        let uu____77327 =
          let uu____77328 =
            let uu____77336 =
              let uu____77337 =
                let uu____77348 =
                  let uu____77349 =
                    let uu____77354 =
                      let uu____77355 =
                        let uu____77358 =
                          let uu____77361 =
                            let uu____77364 =
                              let uu____77365 =
                                let uu____77370 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77371 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77370, uu____77371)  in
                              FStar_SMTEncoding_Util.mkGT uu____77365  in
                            let uu____77373 =
                              let uu____77376 =
                                let uu____77377 =
                                  let uu____77382 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77383 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77382, uu____77383)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77377  in
                              let uu____77385 =
                                let uu____77388 =
                                  let uu____77389 =
                                    let uu____77394 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77395 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77394, uu____77395)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77389  in
                                [uu____77388]  in
                              uu____77376 :: uu____77385  in
                            uu____77364 :: uu____77373  in
                          typing_pred_y :: uu____77361  in
                        typing_pred :: uu____77358  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77355  in
                    (uu____77354, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77349  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77348)
                 in
              let uu____77428 =
                let uu____77443 = FStar_TypeChecker_Env.get_range env  in
                let uu____77444 = mkForall_fuel1 env  in
                uu____77444 uu____77443  in
              uu____77428 uu____77337  in
            (uu____77336,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77328  in
        [uu____77327]  in
      uu____77232 :: uu____77324  in
    uu____77168 :: uu____77229  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77491 =
      let uu____77492 =
        let uu____77500 =
          let uu____77501 = FStar_TypeChecker_Env.get_range env  in
          let uu____77502 =
            let uu____77513 =
              let uu____77518 =
                let uu____77521 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77521]  in
              [uu____77518]  in
            let uu____77526 =
              let uu____77527 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77527 tt  in
            (uu____77513, [bb], uu____77526)  in
          FStar_SMTEncoding_Term.mkForall uu____77501 uu____77502  in
        (uu____77500, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77492  in
    let uu____77552 =
      let uu____77555 =
        let uu____77556 =
          let uu____77564 =
            let uu____77565 =
              let uu____77576 =
                let uu____77577 =
                  let uu____77582 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77582)  in
                FStar_SMTEncoding_Util.mkImp uu____77577  in
              ([[typing_pred]], [xx], uu____77576)  in
            let uu____77609 =
              let uu____77624 = FStar_TypeChecker_Env.get_range env  in
              let uu____77625 = mkForall_fuel1 env  in
              uu____77625 uu____77624  in
            uu____77609 uu____77565  in
          (uu____77564, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77556  in
      [uu____77555]  in
    uu____77491 :: uu____77552  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77672 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77672]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77702 =
      let uu____77703 =
        let uu____77711 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77711, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77703  in
    [uu____77702]  in
  let mk_and_interp env conj uu____77734 =
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
    let uu____77763 =
      let uu____77764 =
        let uu____77772 =
          let uu____77773 = FStar_TypeChecker_Env.get_range env  in
          let uu____77774 =
            let uu____77785 =
              let uu____77786 =
                let uu____77791 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77791, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77786  in
            ([[l_and_a_b]], [aa; bb], uu____77785)  in
          FStar_SMTEncoding_Term.mkForall uu____77773 uu____77774  in
        (uu____77772, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77764  in
    [uu____77763]  in
  let mk_or_interp env disj uu____77846 =
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
    let uu____77875 =
      let uu____77876 =
        let uu____77884 =
          let uu____77885 = FStar_TypeChecker_Env.get_range env  in
          let uu____77886 =
            let uu____77897 =
              let uu____77898 =
                let uu____77903 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77903, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77898  in
            ([[l_or_a_b]], [aa; bb], uu____77897)  in
          FStar_SMTEncoding_Term.mkForall uu____77885 uu____77886  in
        (uu____77884, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77876  in
    [uu____77875]  in
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
    let uu____77981 =
      let uu____77982 =
        let uu____77990 =
          let uu____77991 = FStar_TypeChecker_Env.get_range env  in
          let uu____77992 =
            let uu____78003 =
              let uu____78004 =
                let uu____78009 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78009, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78004  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____78003)  in
          FStar_SMTEncoding_Term.mkForall uu____77991 uu____77992  in
        (uu____77990, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77982  in
    [uu____77981]  in
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
    let uu____78099 =
      let uu____78100 =
        let uu____78108 =
          let uu____78109 = FStar_TypeChecker_Env.get_range env  in
          let uu____78110 =
            let uu____78121 =
              let uu____78122 =
                let uu____78127 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78127, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78122  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78121)  in
          FStar_SMTEncoding_Term.mkForall uu____78109 uu____78110  in
        (uu____78108, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78100  in
    [uu____78099]  in
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
    let uu____78227 =
      let uu____78228 =
        let uu____78236 =
          let uu____78237 = FStar_TypeChecker_Env.get_range env  in
          let uu____78238 =
            let uu____78249 =
              let uu____78250 =
                let uu____78255 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78255, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78250  in
            ([[l_imp_a_b]], [aa; bb], uu____78249)  in
          FStar_SMTEncoding_Term.mkForall uu____78237 uu____78238  in
        (uu____78236, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78228  in
    [uu____78227]  in
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
    let uu____78339 =
      let uu____78340 =
        let uu____78348 =
          let uu____78349 = FStar_TypeChecker_Env.get_range env  in
          let uu____78350 =
            let uu____78361 =
              let uu____78362 =
                let uu____78367 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78367, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78362  in
            ([[l_iff_a_b]], [aa; bb], uu____78361)  in
          FStar_SMTEncoding_Term.mkForall uu____78349 uu____78350  in
        (uu____78348, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78340  in
    [uu____78339]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78438 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78438  in
    let uu____78443 =
      let uu____78444 =
        let uu____78452 =
          let uu____78453 = FStar_TypeChecker_Env.get_range env  in
          let uu____78454 =
            let uu____78465 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78465)  in
          FStar_SMTEncoding_Term.mkForall uu____78453 uu____78454  in
        (uu____78452, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78444  in
    [uu____78443]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78518 =
      let uu____78519 =
        let uu____78527 =
          let uu____78528 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78528 range_ty  in
        let uu____78529 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78527, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78529)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78519  in
    [uu____78518]  in
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
        let uu____78575 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78575 x1 t  in
      let uu____78577 = FStar_TypeChecker_Env.get_range env  in
      let uu____78578 =
        let uu____78589 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78589)  in
      FStar_SMTEncoding_Term.mkForall uu____78577 uu____78578  in
    let uu____78614 =
      let uu____78615 =
        let uu____78623 =
          let uu____78624 = FStar_TypeChecker_Env.get_range env  in
          let uu____78625 =
            let uu____78636 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78636)  in
          FStar_SMTEncoding_Term.mkForall uu____78624 uu____78625  in
        (uu____78623,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78615  in
    [uu____78614]  in
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
    let uu____78697 =
      let uu____78698 =
        let uu____78706 =
          let uu____78707 = FStar_TypeChecker_Env.get_range env  in
          let uu____78708 =
            let uu____78724 =
              let uu____78725 =
                let uu____78730 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78731 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78730, uu____78731)  in
              FStar_SMTEncoding_Util.mkAnd uu____78725  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78724)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78707 uu____78708  in
        (uu____78706,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78698  in
    [uu____78697]  in
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
          let uu____79289 =
            FStar_Util.find_opt
              (fun uu____79327  ->
                 match uu____79327 with
                 | (l,uu____79343) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79289 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79386,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79447 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79447 with
        | (form,decls) ->
            let uu____79456 =
              let uu____79459 =
                let uu____79462 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79462]  in
              FStar_All.pipe_right uu____79459
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79456
  
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
              let uu____79521 =
                ((let uu____79525 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79525) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79521
              then
                let arg_sorts =
                  let uu____79537 =
                    let uu____79538 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79538.FStar_Syntax_Syntax.n  in
                  match uu____79537 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79544) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79582  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79589 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79591 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79591 with
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
                    let uu____79627 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79627, env1)
              else
                (let uu____79632 = prims.is lid  in
                 if uu____79632
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79641 = prims.mk lid vname  in
                   match uu____79641 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79665 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79665, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79674 =
                      let uu____79693 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79693 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79721 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79721
                            then
                              let uu____79726 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79729 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79729.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79729.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79729.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79729.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79729.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79729.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79729.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79729.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79729.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79729.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79729.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79729.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79729.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79729.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79729.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79729.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79729.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79729.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79729.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79729.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79729.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79729.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79729.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79729.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79729.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79729.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79729.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79729.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79729.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79729.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79729.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79729.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79729.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79729.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79729.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79729.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79729.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79729.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79729.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79729.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79729.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79729.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79726
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79752 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79752)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79674 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79858  ->
                                  match uu___639_79858 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79862 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79862 with
                                       | (uu____79895,xxv) ->
                                           let xx =
                                             let uu____79934 =
                                               let uu____79935 =
                                                 let uu____79941 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79941,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79935
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79934
                                              in
                                           let uu____79944 =
                                             let uu____79945 =
                                               let uu____79953 =
                                                 let uu____79954 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79955 =
                                                   let uu____79966 =
                                                     let uu____79967 =
                                                       let uu____79972 =
                                                         let uu____79973 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79973
                                                          in
                                                       (vapp, uu____79972)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79967
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79966)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79954 uu____79955
                                                  in
                                               (uu____79953,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79945
                                              in
                                           [uu____79944])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79988 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79988 with
                                       | (uu____80021,xxv) ->
                                           let xx =
                                             let uu____80060 =
                                               let uu____80061 =
                                                 let uu____80067 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____80067,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____80061
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____80060
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
                                           let uu____80078 =
                                             let uu____80079 =
                                               let uu____80087 =
                                                 let uu____80088 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80089 =
                                                   let uu____80100 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80100)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80088 uu____80089
                                                  in
                                               (uu____80087,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80079
                                              in
                                           [uu____80078])
                                  | uu____80113 -> []))
                           in
                        let uu____80114 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80114 with
                         | (vars,guards,env',decls1,uu____80139) ->
                             let uu____80152 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80165 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80165, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80169 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80169 with
                                    | (g,ds) ->
                                        let uu____80182 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80182,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80152 with
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
                                  let should_thunk uu____80205 =
                                    let is_type1 t =
                                      let uu____80213 =
                                        let uu____80214 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80214.FStar_Syntax_Syntax.n  in
                                      match uu____80213 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80218 -> true
                                      | uu____80220 -> false  in
                                    let is_squash1 t =
                                      let uu____80229 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80229 with
                                      | (head1,uu____80248) ->
                                          let uu____80273 =
                                            let uu____80274 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80274.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80273 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80279;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80280;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80282;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80283;_};_},uu____80284)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80292 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80297 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80297))
                                       &&
                                       (let uu____80303 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80303))
                                      &&
                                      (let uu____80306 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80306)
                                     in
                                  let uu____80308 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80367 -> (false, vars)  in
                                  (match uu____80308 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80417 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80417 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80453 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80462 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80462
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80473 ->
                                                  let uu____80482 =
                                                    let uu____80490 =
                                                      get_vtok ()  in
                                                    (uu____80490, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80482
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80497 =
                                                let uu____80505 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80505)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80497
                                               in
                                            let uu____80519 =
                                              let vname_decl =
                                                let uu____80527 =
                                                  let uu____80539 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80539,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80527
                                                 in
                                              let uu____80550 =
                                                let env2 =
                                                  let uu___1026_80556 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80556.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80557 =
                                                  let uu____80559 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80559
                                                   in
                                                if uu____80557
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80550 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80576 =
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
                                                        let uu____80602 =
                                                          let uu____80605 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80605
                                                           in
                                                        let uu____80612 =
                                                          let uu____80613 =
                                                            let uu____80616 =
                                                              let uu____80617
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80617
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80621  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80621)
                                                              uu____80616
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80613
                                                           in
                                                        (uu____80602,
                                                          uu____80612)
                                                    | uu____80628 when
                                                        thunked ->
                                                        let uu____80639 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80639
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80654
                                                                 =
                                                                 let uu____80662
                                                                   =
                                                                   let uu____80665
                                                                    =
                                                                    let uu____80668
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80668]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80665
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80662)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80654
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80676
                                                               =
                                                               let uu____80684
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80684,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80676
                                                              in
                                                           let uu____80689 =
                                                             let uu____80692
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80692
                                                              in
                                                           (uu____80689,
                                                             env1))
                                                    | uu____80701 ->
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
                                                          let uu____80725 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80726 =
                                                            let uu____80737 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80737)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80725
                                                            uu____80726
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80747 =
                                                            let uu____80755 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80755,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80747
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
                                                            let uu____80766 =
                                                              let uu____80767
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80767]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80766
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80794 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80795 =
                                                              let uu____80806
                                                                =
                                                                let uu____80807
                                                                  =
                                                                  let uu____80812
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80813
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80812,
                                                                    uu____80813)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80807
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80806)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80794
                                                              uu____80795
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80842 =
                                                          let uu____80845 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80845
                                                           in
                                                        (uu____80842, env1)
                                                     in
                                                  (match uu____80576 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80866 =
                                                         let uu____80869 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80869
                                                           tok_decl
                                                          in
                                                       (uu____80866, env2))
                                               in
                                            (match uu____80519 with
                                             | (decls2,env2) ->
                                                 let uu____80888 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80898 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80898 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80913 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80913, decls)
                                                    in
                                                 (match uu____80888 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80928 =
                                                          let uu____80936 =
                                                            let uu____80937 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80938 =
                                                              let uu____80949
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80949)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80937
                                                              uu____80938
                                                             in
                                                          (uu____80936,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80928
                                                         in
                                                      let freshness =
                                                        let uu____80965 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80965
                                                        then
                                                          let uu____80973 =
                                                            let uu____80974 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80975 =
                                                              let uu____80988
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____80995
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80988,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____80995)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80974
                                                              uu____80975
                                                             in
                                                          let uu____81001 =
                                                            let uu____81004 =
                                                              let uu____81005
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____81005
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____81004]  in
                                                          uu____80973 ::
                                                            uu____81001
                                                        else []  in
                                                      let g =
                                                        let uu____81011 =
                                                          let uu____81014 =
                                                            let uu____81017 =
                                                              let uu____81020
                                                                =
                                                                let uu____81023
                                                                  =
                                                                  let uu____81026
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____81026
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____81023
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____81020
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____81017
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____81014
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____81011
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
          let uu____81066 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____81066 with
          | FStar_Pervasives_Native.None  ->
              let uu____81077 = encode_free_var false env x t t_norm []  in
              (match uu____81077 with
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
            let uu____81140 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81140 with
            | (decls,env1) ->
                let uu____81151 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81151
                then
                  let uu____81158 =
                    let uu____81159 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81159  in
                  (uu____81158, env1)
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
             (fun uu____81215  ->
                fun lb  ->
                  match uu____81215 with
                  | (decls,env1) ->
                      let uu____81235 =
                        let uu____81240 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81240
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81235 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81269 = FStar_Syntax_Util.head_and_args t  in
    match uu____81269 with
    | (hd1,args) ->
        let uu____81313 =
          let uu____81314 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81314.FStar_Syntax_Syntax.n  in
        (match uu____81313 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81320,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81344 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81355 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81363 = en  in
    let uu____81364 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81363.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81363.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81363.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81363.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81363.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81363.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81363.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81363.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81363.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81363.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81364
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81394  ->
      fun quals  ->
        match uu____81394 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81499 = FStar_Util.first_N nbinders formals  in
              match uu____81499 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81600  ->
                         fun uu____81601  ->
                           match (uu____81600, uu____81601) with
                           | ((formal,uu____81627),(binder,uu____81629)) ->
                               let uu____81650 =
                                 let uu____81657 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81657)  in
                               FStar_Syntax_Syntax.NT uu____81650) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81671 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81712  ->
                              match uu____81712 with
                              | (x,i) ->
                                  let uu____81731 =
                                    let uu___1139_81732 = x  in
                                    let uu____81733 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81732.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81732.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81733
                                    }  in
                                  (uu____81731, i)))
                       in
                    FStar_All.pipe_right uu____81671
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81757 =
                      let uu____81762 = FStar_Syntax_Subst.compress body  in
                      let uu____81763 =
                        let uu____81764 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81764
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81762
                        uu____81763
                       in
                    uu____81757 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81815 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81815.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81815.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81815.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81815.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81815.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81815.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81815.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81815.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81815.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81815.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81815.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81815.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81815.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81815.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81815.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81815.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81815.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81815.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81815.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81815.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81815.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81815.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81815.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81815.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81815.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81815.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81815.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81815.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81815.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81815.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81815.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81815.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81815.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81815.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81815.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81815.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81815.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81815.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81815.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81815.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81815.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81815.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81887  ->
                       fun uu____81888  ->
                         match (uu____81887, uu____81888) with
                         | ((x,uu____81914),(b,uu____81916)) ->
                             let uu____81937 =
                               let uu____81944 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81944)  in
                             FStar_Syntax_Syntax.NT uu____81937) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81969 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81969
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____81998 ->
                    let uu____82005 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____82005
                | uu____82006 when Prims.op_Negation norm1 ->
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
                | uu____82009 ->
                    let uu____82010 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____82010)
                 in
              let aux t1 e1 =
                let uu____82052 = FStar_Syntax_Util.abs_formals e1  in
                match uu____82052 with
                | (binders,body,lopt) ->
                    let uu____82084 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82100 -> arrow_formals_comp_norm false t1  in
                    (match uu____82084 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82134 =
                           if nformals < nbinders
                           then
                             let uu____82178 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82178 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82262 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82262)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82302 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82302 with
                                | (binders1,body1) ->
                                    let uu____82355 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82355))
                             else
                               (let uu____82368 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82368))
                            in
                         (match uu____82134 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82428 = aux t e  in
              match uu____82428 with
              | (binders,body,comp) ->
                  let uu____82474 =
                    let uu____82485 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82485
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82500 = aux comp1 body1  in
                      match uu____82500 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82474 with
                   | (binders1,body1,comp1) ->
                       let uu____82583 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82583, comp1))
               in
            (try
               (fun uu___1216_82610  ->
                  match () with
                  | () ->
                      let uu____82617 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82617
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82633 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82696  ->
                                   fun lb  ->
                                     match uu____82696 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82751 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82751
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82757 =
                                             let uu____82766 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82766
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82757 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82633 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82907;
                                    FStar_Syntax_Syntax.lbeff = uu____82908;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82910;
                                    FStar_Syntax_Syntax.lbpos = uu____82911;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82935 =
                                     let uu____82942 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82942 with
                                     | (tcenv',uu____82958,e_t) ->
                                         let uu____82964 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82975 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82964 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82992 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82992.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82935 with
                                    | (env',e1,t_norm1) ->
                                        let uu____83002 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____83002 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____83022 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____83022
                                               then
                                                 let uu____83027 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____83030 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____83027 uu____83030
                                               else ());
                                              (let uu____83035 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____83035 with
                                               | (vars,_guards,env'1,binder_decls,uu____83062)
                                                   ->
                                                   let uu____83075 =
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
                                                         let uu____83092 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83092
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83114 =
                                                          let uu____83115 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83116 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83115 fvb
                                                            uu____83116
                                                           in
                                                        (vars, uu____83114))
                                                      in
                                                   (match uu____83075 with
                                                    | (vars1,app) ->
                                                        let uu____83127 =
                                                          let is_logical =
                                                            let uu____83140 =
                                                              let uu____83141
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83141.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83140
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83147 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83151 =
                                                              let uu____83152
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83152
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83151
                                                              (fun lid  ->
                                                                 let uu____83161
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83161
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83162 =
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
                                                          if uu____83162
                                                          then
                                                            let uu____83178 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83179 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83178,
                                                              uu____83179)
                                                          else
                                                            (let uu____83190
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83190))
                                                           in
                                                        (match uu____83127
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83214
                                                                 =
                                                                 let uu____83222
                                                                   =
                                                                   let uu____83223
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83224
                                                                    =
                                                                    let uu____83235
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83235)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83223
                                                                    uu____83224
                                                                    in
                                                                 let uu____83244
                                                                   =
                                                                   let uu____83245
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83245
                                                                    in
                                                                 (uu____83222,
                                                                   uu____83244,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83214
                                                                in
                                                             let uu____83251
                                                               =
                                                               let uu____83254
                                                                 =
                                                                 let uu____83257
                                                                   =
                                                                   let uu____83260
                                                                    =
                                                                    let uu____83263
                                                                    =
                                                                    let uu____83266
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83266
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83263
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83260
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83257
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83254
                                                                in
                                                             (uu____83251,
                                                               env2)))))))
                               | uu____83275 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83335 =
                                   let uu____83341 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83341,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83335  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83347 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83400  ->
                                         fun fvb  ->
                                           match uu____83400 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83455 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83455
                                                  in
                                               let gtok =
                                                 let uu____83459 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83459
                                                  in
                                               let env4 =
                                                 let uu____83462 =
                                                   let uu____83465 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83471  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83471) uu____83465
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83462
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83347 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83591
                                     t_norm uu____83593 =
                                     match (uu____83591, uu____83593) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83623;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83624;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83626;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83627;_})
                                         ->
                                         let uu____83654 =
                                           let uu____83661 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83661 with
                                           | (tcenv',uu____83677,e_t) ->
                                               let uu____83683 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83694 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83683 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83711 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83711.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83654 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83724 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83724
                                                then
                                                  let uu____83729 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83731 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83733 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83729 uu____83731
                                                    uu____83733
                                                else ());
                                               (let uu____83738 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83738 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83765 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83765 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83787 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83787
                                                           then
                                                             let uu____83792
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83794
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83797
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83799
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83792
                                                               uu____83794
                                                               uu____83797
                                                               uu____83799
                                                           else ());
                                                          (let uu____83804 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83804
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83833)
                                                               ->
                                                               let uu____83846
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83859
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83859,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83863
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83863
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83876
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83876,
                                                                    decls0))
                                                                  in
                                                               (match uu____83846
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
                                                                    let uu____83897
                                                                    =
                                                                    let uu____83909
                                                                    =
                                                                    let uu____83912
                                                                    =
                                                                    let uu____83915
                                                                    =
                                                                    let uu____83918
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83918
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83915
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83912
                                                                     in
                                                                    (g,
                                                                    uu____83909,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83897
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
                                                                    let uu____83948
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83948
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
                                                                    let uu____83963
                                                                    =
                                                                    let uu____83966
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83966
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83963
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83972
                                                                    =
                                                                    let uu____83975
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83975
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83972
                                                                     in
                                                                    let uu____83980
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83980
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____83996
                                                                    =
                                                                    let uu____84004
                                                                    =
                                                                    let uu____84005
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84006
                                                                    =
                                                                    let uu____84022
                                                                    =
                                                                    let uu____84023
                                                                    =
                                                                    let uu____84028
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____84028)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____84023
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84022)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____84005
                                                                    uu____84006
                                                                     in
                                                                    let uu____84042
                                                                    =
                                                                    let uu____84043
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____84043
                                                                     in
                                                                    (uu____84004,
                                                                    uu____84042,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83996
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____84050
                                                                    =
                                                                    let uu____84058
                                                                    =
                                                                    let uu____84059
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84060
                                                                    =
                                                                    let uu____84071
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84071)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84059
                                                                    uu____84060
                                                                     in
                                                                    (uu____84058,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84050
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84085
                                                                    =
                                                                    let uu____84093
                                                                    =
                                                                    let uu____84094
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84095
                                                                    =
                                                                    let uu____84106
                                                                    =
                                                                    let uu____84107
                                                                    =
                                                                    let uu____84112
                                                                    =
                                                                    let uu____84113
                                                                    =
                                                                    let uu____84116
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84116
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84113
                                                                     in
                                                                    (gsapp,
                                                                    uu____84112)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84107
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84106)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84094
                                                                    uu____84095
                                                                     in
                                                                    (uu____84093,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84085
                                                                     in
                                                                    let uu____84130
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
                                                                    let uu____84142
                                                                    =
                                                                    let uu____84143
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84143
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84142
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84145
                                                                    =
                                                                    let uu____84153
                                                                    =
                                                                    let uu____84154
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84155
                                                                    =
                                                                    let uu____84166
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84166)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84154
                                                                    uu____84155
                                                                     in
                                                                    (uu____84153,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84145
                                                                     in
                                                                    let uu____84179
                                                                    =
                                                                    let uu____84188
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84188
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84203
                                                                    =
                                                                    let uu____84206
                                                                    =
                                                                    let uu____84207
                                                                    =
                                                                    let uu____84215
                                                                    =
                                                                    let uu____84216
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84217
                                                                    =
                                                                    let uu____84228
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84228)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84216
                                                                    uu____84217
                                                                     in
                                                                    (uu____84215,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84207
                                                                     in
                                                                    [uu____84206]
                                                                     in
                                                                    (d3,
                                                                    uu____84203)
                                                                     in
                                                                    match uu____84179
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84130
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84285
                                                                    =
                                                                    let uu____84288
                                                                    =
                                                                    let uu____84291
                                                                    =
                                                                    let uu____84294
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84294
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84291
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84288
                                                                     in
                                                                    let uu____84301
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84285,
                                                                    uu____84301,
                                                                    env02))))))))))
                                      in
                                   let uu____84306 =
                                     let uu____84319 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84382  ->
                                          fun uu____84383  ->
                                            match (uu____84382, uu____84383)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84508 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84508 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84319
                                      in
                                   (match uu____84306 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84575 =
                                          let isDeclFun uu___640_84592 =
                                            match uu___640_84592 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84594 -> true
                                            | uu____84607 -> false  in
                                          let uu____84609 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84609
                                            (fun decls3  ->
                                               let uu____84639 =
                                                 FStar_List.fold_left
                                                   (fun uu____84670  ->
                                                      fun elt  ->
                                                        match uu____84670
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84711 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84711
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84739
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84739
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
                                                                    let uu___1459_84777
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84777.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84777.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84777.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84639 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84809 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84809, elts, rest))
                                           in
                                        (match uu____84575 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84838 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84844  ->
                                        match uu___641_84844 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84847 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84855 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84855)))
                                in
                             if uu____84838
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84877  ->
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
                   let uu____84916 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84916
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84935 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84935, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84991 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84991 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____84997 = encode_sigelt' env se  in
      match uu____84997 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____85009 =
                  let uu____85012 =
                    let uu____85013 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____85013  in
                  [uu____85012]  in
                FStar_All.pipe_right uu____85009
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____85018 ->
                let uu____85019 =
                  let uu____85022 =
                    let uu____85025 =
                      let uu____85026 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____85026  in
                    [uu____85025]  in
                  FStar_All.pipe_right uu____85022
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____85033 =
                  let uu____85036 =
                    let uu____85039 =
                      let uu____85042 =
                        let uu____85043 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____85043  in
                      [uu____85042]  in
                    FStar_All.pipe_right uu____85039
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____85036  in
                FStar_List.append uu____85019 uu____85033
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____85057 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____85057
       then
         let uu____85062 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____85062
       else ());
      (let is_opaque_to_smt t =
         let uu____85074 =
           let uu____85075 = FStar_Syntax_Subst.compress t  in
           uu____85075.FStar_Syntax_Syntax.n  in
         match uu____85074 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85080)) -> s = "opaque_to_smt"
         | uu____85085 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85094 =
           let uu____85095 = FStar_Syntax_Subst.compress t  in
           uu____85095.FStar_Syntax_Syntax.n  in
         match uu____85094 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85100)) -> s = "uninterpreted_by_smt"
         | uu____85105 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85111 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85117 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85129 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85130 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85131 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85144 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85146 =
             let uu____85148 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85148  in
           if uu____85146
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85177 ->
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
                let uu____85209 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85209 with
                | (formals,uu____85229) ->
                    let arity = FStar_List.length formals  in
                    let uu____85253 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85253 with
                     | (aname,atok,env2) ->
                         let uu____85279 =
                           let uu____85284 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85284 env2
                            in
                         (match uu____85279 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85296 =
                                  let uu____85297 =
                                    let uu____85309 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85329  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85309,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85297
                                   in
                                [uu____85296;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85346 =
                                let aux uu____85392 uu____85393 =
                                  match (uu____85392, uu____85393) with
                                  | ((bv,uu____85437),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85469 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85469 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85492 =
                                             let uu____85495 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85495 :: acc_sorts  in
                                           (env4, uu____85492, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85346 with
                               | (uu____85527,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85543 =
                                       let uu____85551 =
                                         let uu____85552 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85553 =
                                           let uu____85564 =
                                             let uu____85565 =
                                               let uu____85570 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85570)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85565
                                              in
                                           ([[app]], xs_sorts, uu____85564)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85552 uu____85553
                                          in
                                       (uu____85551,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85543
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85585 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85585
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85588 =
                                       let uu____85596 =
                                         let uu____85597 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85598 =
                                           let uu____85609 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85609)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85597 uu____85598
                                          in
                                       (uu____85596,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85588
                                      in
                                   let uu____85622 =
                                     let uu____85625 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85625  in
                                   (env2, uu____85622))))
                 in
              let uu____85634 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85634 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85660,uu____85661)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85662 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85662 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85684,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85691 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85697  ->
                       match uu___642_85697 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85700 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85706 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85709 -> false))
                in
             Prims.op_Negation uu____85691  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85719 =
                let uu____85724 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85724 env fv t quals  in
              match uu____85719 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85738 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85738  in
                  let uu____85741 =
                    let uu____85742 =
                      let uu____85745 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85745
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85742  in
                  (uu____85741, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85755 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85755 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85767 = env  in
                  let uu____85768 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85767.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85767.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85767.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85768;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85767.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85767.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85767.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85767.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85767.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85767.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85767.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85770 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85770 with
                 | (f3,decls) ->
                     let g =
                       let uu____85784 =
                         let uu____85787 =
                           let uu____85788 =
                             let uu____85796 =
                               let uu____85797 =
                                 let uu____85799 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85799
                                  in
                               FStar_Pervasives_Native.Some uu____85797  in
                             let uu____85803 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85796, uu____85803)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85788  in
                         [uu____85787]  in
                       FStar_All.pipe_right uu____85784
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85812) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85826 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85848 =
                        let uu____85851 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85851.FStar_Syntax_Syntax.fv_name  in
                      uu____85848.FStar_Syntax_Syntax.v  in
                    let uu____85852 =
                      let uu____85854 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85854  in
                    if uu____85852
                    then
                      let val_decl =
                        let uu___1629_85886 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85886.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85886.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85886.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85887 = encode_sigelt' env1 val_decl  in
                      match uu____85887 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85826 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85923,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85925;
                           FStar_Syntax_Syntax.lbtyp = uu____85926;
                           FStar_Syntax_Syntax.lbeff = uu____85927;
                           FStar_Syntax_Syntax.lbdef = uu____85928;
                           FStar_Syntax_Syntax.lbattrs = uu____85929;
                           FStar_Syntax_Syntax.lbpos = uu____85930;_}::[]),uu____85931)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85950 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85950 with
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
                  let uu____85988 =
                    let uu____85991 =
                      let uu____85992 =
                        let uu____86000 =
                          let uu____86001 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____86002 =
                            let uu____86013 =
                              let uu____86014 =
                                let uu____86019 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____86019)  in
                              FStar_SMTEncoding_Util.mkEq uu____86014  in
                            ([[b2t_x]], [xx], uu____86013)  in
                          FStar_SMTEncoding_Term.mkForall uu____86001
                            uu____86002
                           in
                        (uu____86000,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85992  in
                    [uu____85991]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85988
                   in
                let uu____86057 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____86057, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____86060,uu____86061) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86071  ->
                   match uu___643_86071 with
                   | FStar_Syntax_Syntax.Discriminator uu____86073 -> true
                   | uu____86075 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86077,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86089 =
                      let uu____86091 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86091.FStar_Ident.idText  in
                    uu____86089 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86098  ->
                      match uu___644_86098 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86101 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86104) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86118  ->
                   match uu___645_86118 with
                   | FStar_Syntax_Syntax.Projector uu____86120 -> true
                   | uu____86126 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86130 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86130 with
            | FStar_Pervasives_Native.Some uu____86137 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86139 = se  in
                  let uu____86140 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86140;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86139.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86139.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86139.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86143) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86158) ->
           let uu____86167 = encode_sigelts env ses  in
           (match uu____86167 with
            | (g,env1) ->
                let uu____86178 =
                  FStar_List.fold_left
                    (fun uu____86202  ->
                       fun elt  ->
                         match uu____86202 with
                         | (g',inversions) ->
                             let uu____86230 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86253  ->
                                       match uu___646_86253 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86255;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86256;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86257;_}
                                           -> false
                                       | uu____86264 -> true))
                                in
                             (match uu____86230 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86289 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86289.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86289.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86289.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86178 with
                 | (g',inversions) ->
                     let uu____86308 =
                       FStar_List.fold_left
                         (fun uu____86339  ->
                            fun elt  ->
                              match uu____86339 with
                              | (decls,elts,rest) ->
                                  let uu____86380 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86389  ->
                                            match uu___647_86389 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86391 -> true
                                            | uu____86404 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86380
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86427 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86448  ->
                                               match uu___648_86448 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86450 -> true
                                               | uu____86463 -> false))
                                        in
                                     match uu____86427 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86494 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86494.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86494.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86494.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86308 with
                      | (decls,elts,rest) ->
                          let uu____86520 =
                            let uu____86521 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86528 =
                              let uu____86531 =
                                let uu____86534 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86534  in
                              FStar_List.append elts uu____86531  in
                            FStar_List.append uu____86521 uu____86528  in
                          (uu____86520, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86545,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86558 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86558 with
             | (usubst,uvs) ->
                 let uu____86578 =
                   let uu____86585 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86586 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86587 =
                     let uu____86588 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86588 k  in
                   (uu____86585, uu____86586, uu____86587)  in
                 (match uu____86578 with
                  | (env1,tps1,k1) ->
                      let uu____86601 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86601 with
                       | (tps2,k2) ->
                           let uu____86609 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86609 with
                            | (uu____86625,k3) ->
                                let uu____86647 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86647 with
                                 | (tps3,env_tps,uu____86659,us) ->
                                     let u_k =
                                       let uu____86662 =
                                         let uu____86663 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86664 =
                                           let uu____86669 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86671 =
                                             let uu____86672 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86672
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86669 uu____86671
                                            in
                                         uu____86664
                                           FStar_Pervasives_Native.None
                                           uu____86663
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86662 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86692) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86698,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86701) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86709,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86716) ->
                                           let uu____86717 =
                                             let uu____86719 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86719
                                              in
                                           failwith uu____86717
                                       | (uu____86723,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86724 =
                                             let uu____86726 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86726
                                              in
                                           failwith uu____86724
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86730,uu____86731) ->
                                           let uu____86740 =
                                             let uu____86742 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86742
                                              in
                                           failwith uu____86740
                                       | (uu____86746,FStar_Syntax_Syntax.U_unif
                                          uu____86747) ->
                                           let uu____86756 =
                                             let uu____86758 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86758
                                              in
                                           failwith uu____86756
                                       | uu____86762 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86775 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86775 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86793 = u_leq_u_k u_tp  in
                                       if uu____86793
                                       then true
                                       else
                                         (let uu____86800 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86800 with
                                          | (formals,uu____86817) ->
                                              let uu____86838 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86838 with
                                               | (uu____86848,uu____86849,uu____86850,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86861 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86861
             then
               let uu____86866 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86866
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86886  ->
                       match uu___649_86886 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86890 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86903 = c  in
                 match uu____86903 with
                 | (name,args,uu____86908,uu____86909,uu____86910) ->
                     let uu____86921 =
                       let uu____86922 =
                         let uu____86934 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86961  ->
                                   match uu____86961 with
                                   | (uu____86970,sort,uu____86972) -> sort))
                            in
                         (name, uu____86934,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86922  in
                     [uu____86921]
               else
                 (let uu____86983 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____86983 c)
                in
             let inversion_axioms tapp vars =
               let uu____87001 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____87009 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____87009 FStar_Option.isNone))
                  in
               if uu____87001
               then []
               else
                 (let uu____87044 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____87044 with
                  | (xxsym,xx) ->
                      let uu____87057 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87096  ->
                                fun l  ->
                                  match uu____87096 with
                                  | (out,decls) ->
                                      let uu____87116 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87116 with
                                       | (uu____87127,data_t) ->
                                           let uu____87129 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87129 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87173 =
                                                    let uu____87174 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87174.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87173 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87177,indices)
                                                      -> indices
                                                  | uu____87203 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87233  ->
                                                            match uu____87233
                                                            with
                                                            | (x,uu____87241)
                                                                ->
                                                                let uu____87246
                                                                  =
                                                                  let uu____87247
                                                                    =
                                                                    let uu____87255
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87255,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87247
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87246)
                                                       env)
                                                   in
                                                let uu____87260 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87260 with
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
                                                                  let uu____87295
                                                                    =
                                                                    let uu____87300
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87300,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87295)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87303 =
                                                         let uu____87304 =
                                                           let uu____87309 =
                                                             let uu____87310
                                                               =
                                                               let uu____87315
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87316
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87315,
                                                                 uu____87316)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87310
                                                              in
                                                           (out, uu____87309)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87304
                                                          in
                                                       (uu____87303,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____87057 with
                       | (data_ax,decls) ->
                           let uu____87331 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87331 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87348 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87348 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87355 =
                                    let uu____87363 =
                                      let uu____87364 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87365 =
                                        let uu____87376 =
                                          let uu____87377 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87379 =
                                            let uu____87382 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87382 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87377 uu____87379
                                           in
                                        let uu____87384 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87376,
                                          uu____87384)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87364 uu____87365
                                       in
                                    let uu____87393 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87363,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87393)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87355
                                   in
                                let uu____87399 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87399)))
                in
             let uu____87406 =
               let uu____87411 =
                 let uu____87412 = FStar_Syntax_Subst.compress k  in
                 uu____87412.FStar_Syntax_Syntax.n  in
               match uu____87411 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87447 -> (tps, k)  in
             match uu____87406 with
             | (formals,res) ->
                 let uu____87454 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87454 with
                  | (formals1,res1) ->
                      let uu____87465 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87465 with
                       | (vars,guards,env',binder_decls,uu____87490) ->
                           let arity = FStar_List.length vars  in
                           let uu____87504 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87504 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87534 =
                                    let uu____87542 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87542)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87534
                                   in
                                let uu____87548 =
                                  let tname_decl =
                                    let uu____87558 =
                                      let uu____87559 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87578 =
                                                  let uu____87580 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87580
                                                   in
                                                let uu____87582 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87578, uu____87582,
                                                  false)))
                                         in
                                      let uu____87586 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87559,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87586, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87558
                                     in
                                  let uu____87594 =
                                    match vars with
                                    | [] ->
                                        let uu____87607 =
                                          let uu____87608 =
                                            let uu____87611 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87617  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87617) uu____87611
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87608
                                           in
                                        ([], uu____87607)
                                    | uu____87624 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87634 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87634
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87650 =
                                            let uu____87658 =
                                              let uu____87659 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87660 =
                                                let uu____87676 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87676)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87659 uu____87660
                                               in
                                            (uu____87658,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87650
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87594 with
                                  | (tok_decls,env2) ->
                                      let uu____87703 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87703
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87548 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87731 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87731 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87753 =
                                                 let uu____87754 =
                                                   let uu____87762 =
                                                     let uu____87763 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87763
                                                      in
                                                   (uu____87762,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87754
                                                  in
                                               [uu____87753]
                                             else []  in
                                           let uu____87771 =
                                             let uu____87774 =
                                               let uu____87777 =
                                                 let uu____87780 =
                                                   let uu____87781 =
                                                     let uu____87789 =
                                                       let uu____87790 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87791 =
                                                         let uu____87802 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87802)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87790
                                                         uu____87791
                                                        in
                                                     (uu____87789,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87781
                                                    in
                                                 [uu____87780]  in
                                               FStar_List.append karr
                                                 uu____87777
                                                in
                                             FStar_All.pipe_right uu____87774
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87771
                                        in
                                     let aux =
                                       let uu____87821 =
                                         let uu____87824 =
                                           inversion_axioms tapp vars  in
                                         let uu____87827 =
                                           let uu____87830 =
                                             let uu____87833 =
                                               let uu____87834 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87834 env2
                                                 tapp vars
                                                in
                                             [uu____87833]  in
                                           FStar_All.pipe_right uu____87830
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87824
                                           uu____87827
                                          in
                                       FStar_List.append kindingAx
                                         uu____87821
                                        in
                                     let g =
                                       let uu____87842 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87842
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87850,uu____87851,uu____87852,uu____87853,uu____87854)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87862,t,uu____87864,n_tps,uu____87866) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87876 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87876 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87924 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87924 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87952 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87952 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____87972 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____87972 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____88051 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____88051,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____88058 =
                                   let uu____88059 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____88059, true)
                                    in
                                 let uu____88067 =
                                   let uu____88074 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88074
                                    in
                                 FStar_All.pipe_right uu____88058 uu____88067
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
                               let uu____88086 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88086 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88098::uu____88099 ->
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
                                            let uu____88148 =
                                              let uu____88149 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88149]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88148
                                             in
                                          let uu____88175 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88176 =
                                            let uu____88187 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88187)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88175 uu____88176
                                      | uu____88214 -> tok_typing  in
                                    let uu____88225 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88225 with
                                     | (vars',guards',env'',decls_formals,uu____88250)
                                         ->
                                         let uu____88263 =
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
                                         (match uu____88263 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88293 ->
                                                    let uu____88302 =
                                                      let uu____88303 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88303
                                                       in
                                                    [uu____88302]
                                                 in
                                              let encode_elim uu____88319 =
                                                let uu____88320 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88320 with
                                                | (head1,args) ->
                                                    let uu____88371 =
                                                      let uu____88372 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88372.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88371 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88384;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88385;_},uu____88386)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88392 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88392
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
                                                                  | uu____88455
                                                                    ->
                                                                    let uu____88456
                                                                    =
                                                                    let uu____88462
                                                                    =
                                                                    let uu____88464
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88464
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88462)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88456
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88487
                                                                    =
                                                                    let uu____88489
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88489
                                                                     in
                                                                    if
                                                                    uu____88487
                                                                    then
                                                                    let uu____88511
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88511]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88514
                                                                =
                                                                let uu____88528
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88585
                                                                     ->
                                                                    fun
                                                                    uu____88586
                                                                     ->
                                                                    match 
                                                                    (uu____88585,
                                                                    uu____88586)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88697
                                                                    =
                                                                    let uu____88705
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88705
                                                                     in
                                                                    (match uu____88697
                                                                    with
                                                                    | 
                                                                    (uu____88719,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88730
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88730
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88735
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88735
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
                                                                  uu____88528
                                                                 in
                                                              (match uu____88514
                                                               with
                                                               | (uu____88756,arg_vars,elim_eqns_or_guards,uu____88759)
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
                                                                    let uu____88786
                                                                    =
                                                                    let uu____88794
                                                                    =
                                                                    let uu____88795
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88796
                                                                    =
                                                                    let uu____88807
                                                                    =
                                                                    let uu____88808
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88808
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88810
                                                                    =
                                                                    let uu____88811
                                                                    =
                                                                    let uu____88816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88816)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88811
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88807,
                                                                    uu____88810)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88795
                                                                    uu____88796
                                                                     in
                                                                    (uu____88794,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88786
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88831
                                                                    =
                                                                    let uu____88832
                                                                    =
                                                                    let uu____88838
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88838,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88832
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88831
                                                                     in
                                                                    let uu____88841
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88841
                                                                    then
                                                                    let x =
                                                                    let uu____88845
                                                                    =
                                                                    let uu____88851
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88851,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88845
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88856
                                                                    =
                                                                    let uu____88864
                                                                    =
                                                                    let uu____88865
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88866
                                                                    =
                                                                    let uu____88877
                                                                    =
                                                                    let uu____88882
                                                                    =
                                                                    let uu____88885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88885]
                                                                     in
                                                                    [uu____88882]
                                                                     in
                                                                    let uu____88890
                                                                    =
                                                                    let uu____88891
                                                                    =
                                                                    let uu____88896
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88898
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88896,
                                                                    uu____88898)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88891
                                                                     in
                                                                    (uu____88877,
                                                                    [x],
                                                                    uu____88890)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88865
                                                                    uu____88866
                                                                     in
                                                                    let uu____88919
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88864,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88919)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88856
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88930
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
                                                                    (let uu____88953
                                                                    =
                                                                    let uu____88954
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88954
                                                                    dapp1  in
                                                                    [uu____88953])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88930
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88961
                                                                    =
                                                                    let uu____88969
                                                                    =
                                                                    let uu____88970
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88971
                                                                    =
                                                                    let uu____88982
                                                                    =
                                                                    let uu____88983
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88983
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88985
                                                                    =
                                                                    let uu____88986
                                                                    =
                                                                    let uu____88991
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88991)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88986
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88982,
                                                                    uu____88985)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88970
                                                                    uu____88971
                                                                     in
                                                                    (uu____88969,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88961)
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
                                                         let uu____89010 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____89010
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
                                                                  | uu____89073
                                                                    ->
                                                                    let uu____89074
                                                                    =
                                                                    let uu____89080
                                                                    =
                                                                    let uu____89082
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89082
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89080)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89074
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89105
                                                                    =
                                                                    let uu____89107
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89107
                                                                     in
                                                                    if
                                                                    uu____89105
                                                                    then
                                                                    let uu____89129
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89129]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89132
                                                                =
                                                                let uu____89146
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89203
                                                                     ->
                                                                    fun
                                                                    uu____89204
                                                                     ->
                                                                    match 
                                                                    (uu____89203,
                                                                    uu____89204)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89315
                                                                    =
                                                                    let uu____89323
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89323
                                                                     in
                                                                    (match uu____89315
                                                                    with
                                                                    | 
                                                                    (uu____89337,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89348
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89348
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89353
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89353
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
                                                                  uu____89146
                                                                 in
                                                              (match uu____89132
                                                               with
                                                               | (uu____89374,arg_vars,elim_eqns_or_guards,uu____89377)
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
                                                                    let uu____89404
                                                                    =
                                                                    let uu____89412
                                                                    =
                                                                    let uu____89413
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89414
                                                                    =
                                                                    let uu____89425
                                                                    =
                                                                    let uu____89426
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89426
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89428
                                                                    =
                                                                    let uu____89429
                                                                    =
                                                                    let uu____89434
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89434)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89429
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89425,
                                                                    uu____89428)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89413
                                                                    uu____89414
                                                                     in
                                                                    (uu____89412,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89404
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89449
                                                                    =
                                                                    let uu____89450
                                                                    =
                                                                    let uu____89456
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89456,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89450
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89449
                                                                     in
                                                                    let uu____89459
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89459
                                                                    then
                                                                    let x =
                                                                    let uu____89463
                                                                    =
                                                                    let uu____89469
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89469,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89463
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89474
                                                                    =
                                                                    let uu____89482
                                                                    =
                                                                    let uu____89483
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89484
                                                                    =
                                                                    let uu____89495
                                                                    =
                                                                    let uu____89500
                                                                    =
                                                                    let uu____89503
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89503]
                                                                     in
                                                                    [uu____89500]
                                                                     in
                                                                    let uu____89508
                                                                    =
                                                                    let uu____89509
                                                                    =
                                                                    let uu____89514
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89516
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89514,
                                                                    uu____89516)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89509
                                                                     in
                                                                    (uu____89495,
                                                                    [x],
                                                                    uu____89508)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89483
                                                                    uu____89484
                                                                     in
                                                                    let uu____89537
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89482,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89537)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89474
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89548
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
                                                                    (let uu____89571
                                                                    =
                                                                    let uu____89572
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89572
                                                                    dapp1  in
                                                                    [uu____89571])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89548
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89579
                                                                    =
                                                                    let uu____89587
                                                                    =
                                                                    let uu____89588
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89589
                                                                    =
                                                                    let uu____89600
                                                                    =
                                                                    let uu____89601
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89601
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89603
                                                                    =
                                                                    let uu____89604
                                                                    =
                                                                    let uu____89609
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89609)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89604
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89600,
                                                                    uu____89603)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89588
                                                                    uu____89589
                                                                     in
                                                                    (uu____89587,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89579)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89626 ->
                                                         ((let uu____89628 =
                                                             let uu____89634
                                                               =
                                                               let uu____89636
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89638
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89636
                                                                 uu____89638
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89634)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89628);
                                                          ([], [])))
                                                 in
                                              let uu____89646 =
                                                encode_elim ()  in
                                              (match uu____89646 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89672 =
                                                       let uu____89675 =
                                                         let uu____89678 =
                                                           let uu____89681 =
                                                             let uu____89684
                                                               =
                                                               let uu____89687
                                                                 =
                                                                 let uu____89690
                                                                   =
                                                                   let uu____89691
                                                                    =
                                                                    let uu____89703
                                                                    =
                                                                    let uu____89704
                                                                    =
                                                                    let uu____89706
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89706
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89704
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89703)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89691
                                                                    in
                                                                 [uu____89690]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89687
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89684
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89717 =
                                                             let uu____89720
                                                               =
                                                               let uu____89723
                                                                 =
                                                                 let uu____89726
                                                                   =
                                                                   let uu____89729
                                                                    =
                                                                    let uu____89732
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89737
                                                                    =
                                                                    let uu____89740
                                                                    =
                                                                    let uu____89741
                                                                    =
                                                                    let uu____89749
                                                                    =
                                                                    let uu____89750
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89751
                                                                    =
                                                                    let uu____89762
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89762)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89750
                                                                    uu____89751
                                                                     in
                                                                    (uu____89749,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89741
                                                                     in
                                                                    let uu____89775
                                                                    =
                                                                    let uu____89778
                                                                    =
                                                                    let uu____89779
                                                                    =
                                                                    let uu____89787
                                                                    =
                                                                    let uu____89788
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89789
                                                                    =
                                                                    let uu____89800
                                                                    =
                                                                    let uu____89801
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89801
                                                                    vars'  in
                                                                    let uu____89803
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89800,
                                                                    uu____89803)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89788
                                                                    uu____89789
                                                                     in
                                                                    (uu____89787,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89779
                                                                     in
                                                                    [uu____89778]
                                                                     in
                                                                    uu____89740
                                                                    ::
                                                                    uu____89775
                                                                     in
                                                                    uu____89732
                                                                    ::
                                                                    uu____89737
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89729
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89726
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89723
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89720
                                                              in
                                                           FStar_List.append
                                                             uu____89681
                                                             uu____89717
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89678
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89675
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89672
                                                      in
                                                   let uu____89820 =
                                                     let uu____89821 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89821 g
                                                      in
                                                   (uu____89820, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89855  ->
              fun se  ->
                match uu____89855 with
                | (g,env1) ->
                    let uu____89875 = encode_sigelt env1 se  in
                    (match uu____89875 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89943 =
        match uu____89943 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____89980 ->
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
                 ((let uu____89988 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____89988
                   then
                     let uu____89993 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____89995 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____89997 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____89993 uu____89995 uu____89997
                   else ());
                  (let uu____90002 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____90002 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____90020 =
                         let uu____90028 =
                           let uu____90030 =
                             let uu____90032 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____90032
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____90030  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____90028
                          in
                       (match uu____90020 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____90052 = FStar_Options.log_queries ()
                                 in
                              if uu____90052
                              then
                                let uu____90055 =
                                  let uu____90057 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____90059 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____90061 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____90057 uu____90059 uu____90061
                                   in
                                FStar_Pervasives_Native.Some uu____90055
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90077 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90087 =
                                let uu____90090 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90090  in
                              FStar_List.append uu____90077 uu____90087  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90102,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90122 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90122 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90143 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90143 with | (uu____90170,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90223  ->
              match uu____90223 with
              | (l,uu____90232,uu____90233) ->
                  let uu____90236 =
                    let uu____90248 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90248, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90236))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90281  ->
              match uu____90281 with
              | (l,uu____90292,uu____90293) ->
                  let uu____90296 =
                    let uu____90297 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90300  -> FStar_SMTEncoding_Term.Echo _90300)
                      uu____90297
                     in
                  let uu____90301 =
                    let uu____90304 =
                      let uu____90305 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90305  in
                    [uu____90304]  in
                  uu____90296 :: uu____90301))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90334 =
      let uu____90337 =
        let uu____90338 = FStar_Util.psmap_empty ()  in
        let uu____90353 =
          let uu____90362 = FStar_Util.psmap_empty ()  in (uu____90362, [])
           in
        let uu____90369 =
          let uu____90371 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90371 FStar_Ident.string_of_lid  in
        let uu____90373 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90338;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90353;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90369;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90373
        }  in
      [uu____90337]  in
    FStar_ST.op_Colon_Equals last_env uu____90334
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90417 = FStar_ST.op_Bang last_env  in
      match uu____90417 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90445 ->
          let uu___2175_90448 = e  in
          let uu____90449 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90448.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90448.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90448.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90448.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90448.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90448.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90448.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90449;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90448.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90448.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90457 = FStar_ST.op_Bang last_env  in
    match uu____90457 with
    | [] -> failwith "Empty env stack"
    | uu____90484::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90516  ->
    let uu____90517 = FStar_ST.op_Bang last_env  in
    match uu____90517 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90577  ->
    let uu____90578 = FStar_ST.op_Bang last_env  in
    match uu____90578 with
    | [] -> failwith "Popping an empty stack"
    | uu____90605::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90642  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90695  ->
         let uu____90696 = snapshot_env ()  in
         match uu____90696 with
         | (env_depth,()) ->
             let uu____90718 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90718 with
              | (varops_depth,()) ->
                  let uu____90740 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90740 with
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
        (fun uu____90798  ->
           let uu____90799 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90799 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90894 = snapshot msg  in () 
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
        | (uu____90940::uu____90941,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90949 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90949.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90949.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90949.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90950 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_90977 = elt  in
        let uu____90978 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_90977.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_90977.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____90978;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_90977.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____90998 =
        let uu____91001 =
          let uu____91002 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____91002  in
        let uu____91003 = open_fact_db_tags env  in uu____91001 ::
          uu____91003
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____90998
  
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
      let uu____91030 = encode_sigelt env se  in
      match uu____91030 with
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
                (let uu____91076 =
                   let uu____91079 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91079
                    in
                 match uu____91076 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91094 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91094
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91124 = FStar_Options.log_queries ()  in
        if uu____91124
        then
          let uu____91129 =
            let uu____91130 =
              let uu____91132 =
                let uu____91134 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91134 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91132  in
            FStar_SMTEncoding_Term.Caption uu____91130  in
          uu____91129 :: decls
        else decls  in
      (let uu____91153 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91153
       then
         let uu____91156 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91156
       else ());
      (let env =
         let uu____91162 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91162 tcenv  in
       let uu____91163 = encode_top_level_facts env se  in
       match uu____91163 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91177 =
               let uu____91180 =
                 let uu____91183 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91183
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91180  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91177)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91216 = FStar_Options.log_queries ()  in
          if uu____91216
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91236 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91236.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91236.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91236.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91236.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91236.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91236.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91236.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91236.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91236.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91236.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91241 =
             let uu____91244 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91244
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91241  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91264 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91264
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
          (let uu____91288 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91288
           then
             let uu____91291 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91291
           else ());
          (let env =
             let uu____91299 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91299
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91338  ->
                     fun se  ->
                       match uu____91338 with
                       | (g,env2) ->
                           let uu____91358 = encode_top_level_facts env2 se
                              in
                           (match uu____91358 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91381 =
             encode_signature
               (let uu___2303_91390 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91390.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91390.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91390.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91390.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91390.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91390.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91390.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91390.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91390.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91390.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91381 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91406 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91406
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91412 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91412))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91440  ->
        match uu____91440 with
        | (decls,fvbs) ->
            ((let uu____91454 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91454
              then ()
              else
                (let uu____91459 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91459
                 then
                   let uu____91462 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91462
                 else ()));
             (let env =
                let uu____91470 = get_env name tcenv  in
                FStar_All.pipe_right uu____91470
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91472 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91472
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91486 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91486
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
        (let uu____91548 =
           let uu____91550 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91550.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91548);
        (let env =
           let uu____91552 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91552 tcenv  in
         let uu____91553 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91592 = aux rest  in
                 (match uu____91592 with
                  | (out,rest1) ->
                      let t =
                        let uu____91620 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91620 with
                        | FStar_Pervasives_Native.Some uu____91623 ->
                            let uu____91624 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91624
                              x.FStar_Syntax_Syntax.sort
                        | uu____91625 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91629 =
                        let uu____91632 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91635 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91635.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91635.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91632 :: out  in
                      (uu____91629, rest1))
             | uu____91640 -> ([], bindings)  in
           let uu____91647 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91647 with
           | (closing,bindings) ->
               let uu____91674 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91674, bindings)
            in
         match uu____91553 with
         | (q1,bindings) ->
             let uu____91705 = encode_env_bindings env bindings  in
             (match uu____91705 with
              | (env_decls,env1) ->
                  ((let uu____91727 =
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
                    if uu____91727
                    then
                      let uu____91734 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91734
                    else ());
                   (let uu____91739 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91739 with
                    | (phi,qdecls) ->
                        let uu____91760 =
                          let uu____91765 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91765 phi
                           in
                        (match uu____91760 with
                         | (labels,phi1) ->
                             let uu____91782 = encode_labels labels  in
                             (match uu____91782 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91818 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91818
                                    then
                                      let uu____91823 =
                                        let uu____91824 =
                                          let uu____91826 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91826
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91824
                                         in
                                      [uu____91823]
                                    else []  in
                                  let query_prelude =
                                    let uu____91834 =
                                      let uu____91835 =
                                        let uu____91836 =
                                          let uu____91839 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91846 =
                                            let uu____91849 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91849
                                             in
                                          FStar_List.append uu____91839
                                            uu____91846
                                           in
                                        FStar_List.append env_decls
                                          uu____91836
                                         in
                                      FStar_All.pipe_right uu____91835
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91834
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91859 =
                                      let uu____91867 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91868 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91867,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91868)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91859
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
  