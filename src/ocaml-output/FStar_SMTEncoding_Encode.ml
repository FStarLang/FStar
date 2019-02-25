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
  let uu____72756 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72756 with
  | (asym,a) ->
      let uu____72767 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72767 with
       | (xsym,x) ->
           let uu____72778 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72778 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72856 =
                      let uu____72868 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72868, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72856  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72888 =
                      let uu____72896 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72896)  in
                    FStar_SMTEncoding_Util.mkApp uu____72888  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____72915 =
                    let uu____72918 =
                      let uu____72921 =
                        let uu____72924 =
                          let uu____72925 =
                            let uu____72933 =
                              let uu____72934 =
                                let uu____72945 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____72945)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____72934
                               in
                            (uu____72933, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____72925  in
                        let uu____72957 =
                          let uu____72960 =
                            let uu____72961 =
                              let uu____72969 =
                                let uu____72970 =
                                  let uu____72981 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____72981)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____72970
                                 in
                              (uu____72969,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____72961  in
                          [uu____72960]  in
                        uu____72924 :: uu____72957  in
                      xtok_decl :: uu____72921  in
                    xname_decl :: uu____72918  in
                  (xtok1, (FStar_List.length vars), uu____72915)  in
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
                  let uu____73151 =
                    let uu____73172 =
                      let uu____73191 =
                        let uu____73192 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73192
                         in
                      quant axy uu____73191  in
                    (FStar_Parser_Const.op_Eq, uu____73172)  in
                  let uu____73209 =
                    let uu____73232 =
                      let uu____73253 =
                        let uu____73272 =
                          let uu____73273 =
                            let uu____73274 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73274  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73273
                           in
                        quant axy uu____73272  in
                      (FStar_Parser_Const.op_notEq, uu____73253)  in
                    let uu____73291 =
                      let uu____73314 =
                        let uu____73335 =
                          let uu____73354 =
                            let uu____73355 =
                              let uu____73356 =
                                let uu____73361 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73362 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73361, uu____73362)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73356  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73355
                             in
                          quant xy uu____73354  in
                        (FStar_Parser_Const.op_And, uu____73335)  in
                      let uu____73379 =
                        let uu____73402 =
                          let uu____73423 =
                            let uu____73442 =
                              let uu____73443 =
                                let uu____73444 =
                                  let uu____73449 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73450 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73449, uu____73450)  in
                                FStar_SMTEncoding_Util.mkOr uu____73444  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73443
                               in
                            quant xy uu____73442  in
                          (FStar_Parser_Const.op_Or, uu____73423)  in
                        let uu____73467 =
                          let uu____73490 =
                            let uu____73511 =
                              let uu____73530 =
                                let uu____73531 =
                                  let uu____73532 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73532
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73531
                                 in
                              quant qx uu____73530  in
                            (FStar_Parser_Const.op_Negation, uu____73511)  in
                          let uu____73549 =
                            let uu____73572 =
                              let uu____73593 =
                                let uu____73612 =
                                  let uu____73613 =
                                    let uu____73614 =
                                      let uu____73619 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73620 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73619, uu____73620)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73614
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73613
                                   in
                                quant xy uu____73612  in
                              (FStar_Parser_Const.op_LT, uu____73593)  in
                            let uu____73637 =
                              let uu____73660 =
                                let uu____73681 =
                                  let uu____73700 =
                                    let uu____73701 =
                                      let uu____73702 =
                                        let uu____73707 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73708 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73707, uu____73708)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73702
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73701
                                     in
                                  quant xy uu____73700  in
                                (FStar_Parser_Const.op_LTE, uu____73681)  in
                              let uu____73725 =
                                let uu____73748 =
                                  let uu____73769 =
                                    let uu____73788 =
                                      let uu____73789 =
                                        let uu____73790 =
                                          let uu____73795 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73796 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73795, uu____73796)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73790
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73789
                                       in
                                    quant xy uu____73788  in
                                  (FStar_Parser_Const.op_GT, uu____73769)  in
                                let uu____73813 =
                                  let uu____73836 =
                                    let uu____73857 =
                                      let uu____73876 =
                                        let uu____73877 =
                                          let uu____73878 =
                                            let uu____73883 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73884 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73883, uu____73884)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73878
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73877
                                         in
                                      quant xy uu____73876  in
                                    (FStar_Parser_Const.op_GTE, uu____73857)
                                     in
                                  let uu____73901 =
                                    let uu____73924 =
                                      let uu____73945 =
                                        let uu____73964 =
                                          let uu____73965 =
                                            let uu____73966 =
                                              let uu____73971 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____73972 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____73971, uu____73972)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____73966
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____73965
                                           in
                                        quant xy uu____73964  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____73945)
                                       in
                                    let uu____73989 =
                                      let uu____74012 =
                                        let uu____74033 =
                                          let uu____74052 =
                                            let uu____74053 =
                                              let uu____74054 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74054
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74053
                                             in
                                          quant qx uu____74052  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74033)
                                         in
                                      let uu____74071 =
                                        let uu____74094 =
                                          let uu____74115 =
                                            let uu____74134 =
                                              let uu____74135 =
                                                let uu____74136 =
                                                  let uu____74141 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74142 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74141, uu____74142)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74136
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74135
                                               in
                                            quant xy uu____74134  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74115)
                                           in
                                        let uu____74159 =
                                          let uu____74182 =
                                            let uu____74203 =
                                              let uu____74222 =
                                                let uu____74223 =
                                                  let uu____74224 =
                                                    let uu____74229 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74230 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74229,
                                                      uu____74230)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74224
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74223
                                                 in
                                              quant xy uu____74222  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74203)
                                             in
                                          let uu____74247 =
                                            let uu____74270 =
                                              let uu____74291 =
                                                let uu____74310 =
                                                  let uu____74311 =
                                                    let uu____74312 =
                                                      let uu____74317 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74318 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74317,
                                                        uu____74318)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74312
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74311
                                                   in
                                                quant xy uu____74310  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74291)
                                               in
                                            let uu____74335 =
                                              let uu____74358 =
                                                let uu____74379 =
                                                  let uu____74398 =
                                                    let uu____74399 =
                                                      let uu____74400 =
                                                        let uu____74405 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74406 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74405,
                                                          uu____74406)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74400
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74399
                                                     in
                                                  quant xy uu____74398  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74379)
                                                 in
                                              let uu____74423 =
                                                let uu____74446 =
                                                  let uu____74467 =
                                                    let uu____74486 =
                                                      let uu____74487 =
                                                        let uu____74488 =
                                                          let uu____74493 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74494 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74493,
                                                            uu____74494)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74488
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74487
                                                       in
                                                    quant xy uu____74486  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74467)
                                                   in
                                                let uu____74511 =
                                                  let uu____74534 =
                                                    let uu____74555 =
                                                      let uu____74574 =
                                                        let uu____74575 =
                                                          let uu____74576 =
                                                            let uu____74581 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74582 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74581,
                                                              uu____74582)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74576
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74575
                                                         in
                                                      quant xy uu____74574
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74555)
                                                     in
                                                  let uu____74599 =
                                                    let uu____74622 =
                                                      let uu____74643 =
                                                        let uu____74662 =
                                                          let uu____74663 =
                                                            let uu____74664 =
                                                              let uu____74669
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74670
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74669,
                                                                uu____74670)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74664
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74663
                                                           in
                                                        quant xy uu____74662
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74643)
                                                       in
                                                    let uu____74687 =
                                                      let uu____74710 =
                                                        let uu____74731 =
                                                          let uu____74750 =
                                                            let uu____74751 =
                                                              let uu____74752
                                                                =
                                                                let uu____74757
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74758
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74757,
                                                                  uu____74758)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74752
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74751
                                                             in
                                                          quant xy
                                                            uu____74750
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74731)
                                                         in
                                                      let uu____74775 =
                                                        let uu____74798 =
                                                          let uu____74819 =
                                                            let uu____74838 =
                                                              let uu____74839
                                                                =
                                                                let uu____74840
                                                                  =
                                                                  let uu____74845
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74846
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74845,
                                                                    uu____74846)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74840
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74839
                                                               in
                                                            quant xy
                                                              uu____74838
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74819)
                                                           in
                                                        let uu____74863 =
                                                          let uu____74886 =
                                                            let uu____74907 =
                                                              let uu____74926
                                                                =
                                                                let uu____74927
                                                                  =
                                                                  let uu____74928
                                                                    =
                                                                    let uu____74933
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74934
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74933,
                                                                    uu____74934)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____74928
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____74927
                                                                 in
                                                              quant xy
                                                                uu____74926
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74907)
                                                             in
                                                          let uu____74951 =
                                                            let uu____74974 =
                                                              let uu____74995
                                                                =
                                                                let uu____75014
                                                                  =
                                                                  let uu____75015
                                                                    =
                                                                    let uu____75016
                                                                    =
                                                                    let uu____75021
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75022
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75021,
                                                                    uu____75022)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75016
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75015
                                                                   in
                                                                quant xy
                                                                  uu____75014
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____74995)
                                                               in
                                                            let uu____75039 =
                                                              let uu____75062
                                                                =
                                                                let uu____75083
                                                                  =
                                                                  let uu____75102
                                                                    =
                                                                    let uu____75103
                                                                    =
                                                                    let uu____75104
                                                                    =
                                                                    let uu____75109
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75110
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75109,
                                                                    uu____75110)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75104
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75103
                                                                     in
                                                                  quant xy
                                                                    uu____75102
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75083)
                                                                 in
                                                              let uu____75127
                                                                =
                                                                let uu____75150
                                                                  =
                                                                  let uu____75171
                                                                    =
                                                                    let uu____75190
                                                                    =
                                                                    let uu____75191
                                                                    =
                                                                    let uu____75192
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75192
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75191
                                                                     in
                                                                    quant qx
                                                                    uu____75190
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75171)
                                                                   in
                                                                [uu____75150]
                                                                 in
                                                              uu____75062 ::
                                                                uu____75127
                                                               in
                                                            uu____74974 ::
                                                              uu____75039
                                                             in
                                                          uu____74886 ::
                                                            uu____74951
                                                           in
                                                        uu____74798 ::
                                                          uu____74863
                                                         in
                                                      uu____74710 ::
                                                        uu____74775
                                                       in
                                                    uu____74622 ::
                                                      uu____74687
                                                     in
                                                  uu____74534 :: uu____74599
                                                   in
                                                uu____74446 :: uu____74511
                                                 in
                                              uu____74358 :: uu____74423  in
                                            uu____74270 :: uu____74335  in
                                          uu____74182 :: uu____74247  in
                                        uu____74094 :: uu____74159  in
                                      uu____74012 :: uu____74071  in
                                    uu____73924 :: uu____73989  in
                                  uu____73836 :: uu____73901  in
                                uu____73748 :: uu____73813  in
                              uu____73660 :: uu____73725  in
                            uu____73572 :: uu____73637  in
                          uu____73490 :: uu____73549  in
                        uu____73402 :: uu____73467  in
                      uu____73314 :: uu____73379  in
                    uu____73232 :: uu____73291  in
                  uu____73151 :: uu____73209  in
                let mk1 l v1 =
                  let uu____75731 =
                    let uu____75743 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75833  ->
                              match uu____75833 with
                              | (l',uu____75854) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75743
                      (FStar_Option.map
                         (fun uu____75953  ->
                            match uu____75953 with
                            | (uu____75981,b) ->
                                let uu____76015 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76015 v1))
                     in
                  FStar_All.pipe_right uu____75731 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76098  ->
                          match uu____76098 with
                          | (l',uu____76119) -> FStar_Ident.lid_equals l l'))
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
          let uu____76193 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76193 with
          | (xxsym,xx) ->
              let uu____76204 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76204 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76220 =
                     let uu____76228 =
                       let uu____76229 =
                         let uu____76240 =
                           let uu____76241 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76251 =
                             let uu____76262 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76262 :: vars  in
                           uu____76241 :: uu____76251  in
                         let uu____76288 =
                           let uu____76289 =
                             let uu____76294 =
                               let uu____76295 =
                                 let uu____76300 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76300)  in
                               FStar_SMTEncoding_Util.mkEq uu____76295  in
                             (xx_has_type, uu____76294)  in
                           FStar_SMTEncoding_Util.mkImp uu____76289  in
                         ([[xx_has_type]], uu____76240, uu____76288)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76229  in
                     let uu____76313 =
                       let uu____76315 =
                         let uu____76317 =
                           let uu____76319 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76319  in
                         Prims.op_Hat module_name uu____76317  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76315
                        in
                     (uu____76228,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76313)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76220)
  
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
    let uu____76375 =
      let uu____76377 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76377  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76375  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76399 =
      let uu____76400 =
        let uu____76408 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76408, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76400  in
    let uu____76413 =
      let uu____76416 =
        let uu____76417 =
          let uu____76425 =
            let uu____76426 =
              let uu____76437 =
                let uu____76438 =
                  let uu____76443 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76443)  in
                FStar_SMTEncoding_Util.mkImp uu____76438  in
              ([[typing_pred]], [xx], uu____76437)  in
            let uu____76468 =
              let uu____76483 = FStar_TypeChecker_Env.get_range env  in
              let uu____76484 = mkForall_fuel1 env  in
              uu____76484 uu____76483  in
            uu____76468 uu____76426  in
          (uu____76425, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76417  in
      [uu____76416]  in
    uu____76399 :: uu____76413  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76531 =
      let uu____76532 =
        let uu____76540 =
          let uu____76541 = FStar_TypeChecker_Env.get_range env  in
          let uu____76542 =
            let uu____76553 =
              let uu____76558 =
                let uu____76561 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76561]  in
              [uu____76558]  in
            let uu____76566 =
              let uu____76567 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76567 tt  in
            (uu____76553, [bb], uu____76566)  in
          FStar_SMTEncoding_Term.mkForall uu____76541 uu____76542  in
        (uu____76540, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76532  in
    let uu____76592 =
      let uu____76595 =
        let uu____76596 =
          let uu____76604 =
            let uu____76605 =
              let uu____76616 =
                let uu____76617 =
                  let uu____76622 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76622)  in
                FStar_SMTEncoding_Util.mkImp uu____76617  in
              ([[typing_pred]], [xx], uu____76616)  in
            let uu____76649 =
              let uu____76664 = FStar_TypeChecker_Env.get_range env  in
              let uu____76665 = mkForall_fuel1 env  in
              uu____76665 uu____76664  in
            uu____76649 uu____76605  in
          (uu____76604, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76596  in
      [uu____76595]  in
    uu____76531 :: uu____76592  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76708 =
        let uu____76709 =
          let uu____76715 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76715, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76709  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76708  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76729 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76729  in
    let uu____76734 =
      let uu____76735 =
        let uu____76743 =
          let uu____76744 = FStar_TypeChecker_Env.get_range env  in
          let uu____76745 =
            let uu____76756 =
              let uu____76761 =
                let uu____76764 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76764]  in
              [uu____76761]  in
            let uu____76769 =
              let uu____76770 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76770 tt  in
            (uu____76756, [bb], uu____76769)  in
          FStar_SMTEncoding_Term.mkForall uu____76744 uu____76745  in
        (uu____76743, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76735  in
    let uu____76795 =
      let uu____76798 =
        let uu____76799 =
          let uu____76807 =
            let uu____76808 =
              let uu____76819 =
                let uu____76820 =
                  let uu____76825 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76825)  in
                FStar_SMTEncoding_Util.mkImp uu____76820  in
              ([[typing_pred]], [xx], uu____76819)  in
            let uu____76852 =
              let uu____76867 = FStar_TypeChecker_Env.get_range env  in
              let uu____76868 = mkForall_fuel1 env  in
              uu____76868 uu____76867  in
            uu____76852 uu____76808  in
          (uu____76807, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76799  in
      let uu____76890 =
        let uu____76893 =
          let uu____76894 =
            let uu____76902 =
              let uu____76903 =
                let uu____76914 =
                  let uu____76915 =
                    let uu____76920 =
                      let uu____76921 =
                        let uu____76924 =
                          let uu____76927 =
                            let uu____76930 =
                              let uu____76931 =
                                let uu____76936 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____76937 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____76936, uu____76937)  in
                              FStar_SMTEncoding_Util.mkGT uu____76931  in
                            let uu____76939 =
                              let uu____76942 =
                                let uu____76943 =
                                  let uu____76948 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____76949 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____76948, uu____76949)  in
                                FStar_SMTEncoding_Util.mkGTE uu____76943  in
                              let uu____76951 =
                                let uu____76954 =
                                  let uu____76955 =
                                    let uu____76960 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____76961 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____76960, uu____76961)  in
                                  FStar_SMTEncoding_Util.mkLT uu____76955  in
                                [uu____76954]  in
                              uu____76942 :: uu____76951  in
                            uu____76930 :: uu____76939  in
                          typing_pred_y :: uu____76927  in
                        typing_pred :: uu____76924  in
                      FStar_SMTEncoding_Util.mk_and_l uu____76921  in
                    (uu____76920, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____76915  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____76914)
                 in
              let uu____76994 =
                let uu____77009 = FStar_TypeChecker_Env.get_range env  in
                let uu____77010 = mkForall_fuel1 env  in
                uu____77010 uu____77009  in
              uu____76994 uu____76903  in
            (uu____76902,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76894  in
        [uu____76893]  in
      uu____76798 :: uu____76890  in
    uu____76734 :: uu____76795  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77053 =
        let uu____77054 =
          let uu____77060 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77060, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77054  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77053  in
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
      let uu____77076 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77076  in
    let uu____77081 =
      let uu____77082 =
        let uu____77090 =
          let uu____77091 = FStar_TypeChecker_Env.get_range env  in
          let uu____77092 =
            let uu____77103 =
              let uu____77108 =
                let uu____77111 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77111]  in
              [uu____77108]  in
            let uu____77116 =
              let uu____77117 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77117 tt  in
            (uu____77103, [bb], uu____77116)  in
          FStar_SMTEncoding_Term.mkForall uu____77091 uu____77092  in
        (uu____77090, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77082  in
    let uu____77142 =
      let uu____77145 =
        let uu____77146 =
          let uu____77154 =
            let uu____77155 =
              let uu____77166 =
                let uu____77167 =
                  let uu____77172 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77172)  in
                FStar_SMTEncoding_Util.mkImp uu____77167  in
              ([[typing_pred]], [xx], uu____77166)  in
            let uu____77199 =
              let uu____77214 = FStar_TypeChecker_Env.get_range env  in
              let uu____77215 = mkForall_fuel1 env  in
              uu____77215 uu____77214  in
            uu____77199 uu____77155  in
          (uu____77154, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77146  in
      let uu____77237 =
        let uu____77240 =
          let uu____77241 =
            let uu____77249 =
              let uu____77250 =
                let uu____77261 =
                  let uu____77262 =
                    let uu____77267 =
                      let uu____77268 =
                        let uu____77271 =
                          let uu____77274 =
                            let uu____77277 =
                              let uu____77278 =
                                let uu____77283 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77284 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77283, uu____77284)  in
                              FStar_SMTEncoding_Util.mkGT uu____77278  in
                            let uu____77286 =
                              let uu____77289 =
                                let uu____77290 =
                                  let uu____77295 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77296 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77295, uu____77296)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77290  in
                              let uu____77298 =
                                let uu____77301 =
                                  let uu____77302 =
                                    let uu____77307 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77308 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77307, uu____77308)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77302  in
                                [uu____77301]  in
                              uu____77289 :: uu____77298  in
                            uu____77277 :: uu____77286  in
                          typing_pred_y :: uu____77274  in
                        typing_pred :: uu____77271  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77268  in
                    (uu____77267, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77262  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77261)
                 in
              let uu____77341 =
                let uu____77356 = FStar_TypeChecker_Env.get_range env  in
                let uu____77357 = mkForall_fuel1 env  in
                uu____77357 uu____77356  in
              uu____77341 uu____77250  in
            (uu____77249,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77241  in
        [uu____77240]  in
      uu____77145 :: uu____77237  in
    uu____77081 :: uu____77142  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77404 =
      let uu____77405 =
        let uu____77413 =
          let uu____77414 = FStar_TypeChecker_Env.get_range env  in
          let uu____77415 =
            let uu____77426 =
              let uu____77431 =
                let uu____77434 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77434]  in
              [uu____77431]  in
            let uu____77439 =
              let uu____77440 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77440 tt  in
            (uu____77426, [bb], uu____77439)  in
          FStar_SMTEncoding_Term.mkForall uu____77414 uu____77415  in
        (uu____77413, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77405  in
    let uu____77465 =
      let uu____77468 =
        let uu____77469 =
          let uu____77477 =
            let uu____77478 =
              let uu____77489 =
                let uu____77490 =
                  let uu____77495 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77495)  in
                FStar_SMTEncoding_Util.mkImp uu____77490  in
              ([[typing_pred]], [xx], uu____77489)  in
            let uu____77522 =
              let uu____77537 = FStar_TypeChecker_Env.get_range env  in
              let uu____77538 = mkForall_fuel1 env  in
              uu____77538 uu____77537  in
            uu____77522 uu____77478  in
          (uu____77477, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77469  in
      [uu____77468]  in
    uu____77404 :: uu____77465  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77585 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77585]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77615 =
      let uu____77616 =
        let uu____77624 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77624, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77616  in
    [uu____77615]  in
  let mk_and_interp env conj uu____77647 =
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
    let uu____77676 =
      let uu____77677 =
        let uu____77685 =
          let uu____77686 = FStar_TypeChecker_Env.get_range env  in
          let uu____77687 =
            let uu____77698 =
              let uu____77699 =
                let uu____77704 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77704, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77699  in
            ([[l_and_a_b]], [aa; bb], uu____77698)  in
          FStar_SMTEncoding_Term.mkForall uu____77686 uu____77687  in
        (uu____77685, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77677  in
    [uu____77676]  in
  let mk_or_interp env disj uu____77759 =
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
    let uu____77788 =
      let uu____77789 =
        let uu____77797 =
          let uu____77798 = FStar_TypeChecker_Env.get_range env  in
          let uu____77799 =
            let uu____77810 =
              let uu____77811 =
                let uu____77816 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77816, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77811  in
            ([[l_or_a_b]], [aa; bb], uu____77810)  in
          FStar_SMTEncoding_Term.mkForall uu____77798 uu____77799  in
        (uu____77797, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77789  in
    [uu____77788]  in
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
    let uu____77894 =
      let uu____77895 =
        let uu____77903 =
          let uu____77904 = FStar_TypeChecker_Env.get_range env  in
          let uu____77905 =
            let uu____77916 =
              let uu____77917 =
                let uu____77922 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____77922, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77917  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____77916)  in
          FStar_SMTEncoding_Term.mkForall uu____77904 uu____77905  in
        (uu____77903, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77895  in
    [uu____77894]  in
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
    let uu____78012 =
      let uu____78013 =
        let uu____78021 =
          let uu____78022 = FStar_TypeChecker_Env.get_range env  in
          let uu____78023 =
            let uu____78034 =
              let uu____78035 =
                let uu____78040 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78040, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78035  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78034)  in
          FStar_SMTEncoding_Term.mkForall uu____78022 uu____78023  in
        (uu____78021, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78013  in
    [uu____78012]  in
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
    let uu____78140 =
      let uu____78141 =
        let uu____78149 =
          let uu____78150 = FStar_TypeChecker_Env.get_range env  in
          let uu____78151 =
            let uu____78162 =
              let uu____78163 =
                let uu____78168 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78168, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78163  in
            ([[l_imp_a_b]], [aa; bb], uu____78162)  in
          FStar_SMTEncoding_Term.mkForall uu____78150 uu____78151  in
        (uu____78149, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78141  in
    [uu____78140]  in
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
    let uu____78252 =
      let uu____78253 =
        let uu____78261 =
          let uu____78262 = FStar_TypeChecker_Env.get_range env  in
          let uu____78263 =
            let uu____78274 =
              let uu____78275 =
                let uu____78280 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78280, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78275  in
            ([[l_iff_a_b]], [aa; bb], uu____78274)  in
          FStar_SMTEncoding_Term.mkForall uu____78262 uu____78263  in
        (uu____78261, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78253  in
    [uu____78252]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78351 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78351  in
    let uu____78356 =
      let uu____78357 =
        let uu____78365 =
          let uu____78366 = FStar_TypeChecker_Env.get_range env  in
          let uu____78367 =
            let uu____78378 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78378)  in
          FStar_SMTEncoding_Term.mkForall uu____78366 uu____78367  in
        (uu____78365, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78357  in
    [uu____78356]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78431 =
      let uu____78432 =
        let uu____78440 =
          let uu____78441 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78441 range_ty  in
        let uu____78442 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78440, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78442)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78432  in
    [uu____78431]  in
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
        let uu____78488 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78488 x1 t  in
      let uu____78490 = FStar_TypeChecker_Env.get_range env  in
      let uu____78491 =
        let uu____78502 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78502)  in
      FStar_SMTEncoding_Term.mkForall uu____78490 uu____78491  in
    let uu____78527 =
      let uu____78528 =
        let uu____78536 =
          let uu____78537 = FStar_TypeChecker_Env.get_range env  in
          let uu____78538 =
            let uu____78549 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78549)  in
          FStar_SMTEncoding_Term.mkForall uu____78537 uu____78538  in
        (uu____78536,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78528  in
    [uu____78527]  in
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
    let uu____78610 =
      let uu____78611 =
        let uu____78619 =
          let uu____78620 = FStar_TypeChecker_Env.get_range env  in
          let uu____78621 =
            let uu____78637 =
              let uu____78638 =
                let uu____78643 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78644 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78643, uu____78644)  in
              FStar_SMTEncoding_Util.mkAnd uu____78638  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78637)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78620 uu____78621  in
        (uu____78619,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78611  in
    [uu____78610]  in
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
          let uu____79202 =
            FStar_Util.find_opt
              (fun uu____79240  ->
                 match uu____79240 with
                 | (l,uu____79256) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79202 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79299,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79360 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79360 with
        | (form,decls) ->
            let uu____79369 =
              let uu____79372 =
                let uu____79375 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79375]  in
              FStar_All.pipe_right uu____79372
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79369
  
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
              let uu____79434 =
                ((let uu____79438 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79438) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79434
              then
                let arg_sorts =
                  let uu____79450 =
                    let uu____79451 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79451.FStar_Syntax_Syntax.n  in
                  match uu____79450 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79457) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79495  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79502 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79504 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79504 with
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
                    let uu____79540 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79540, env1)
              else
                (let uu____79545 = prims.is lid  in
                 if uu____79545
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79554 = prims.mk lid vname  in
                   match uu____79554 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79578 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79578, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79587 =
                      let uu____79606 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79606 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79634 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79634
                            then
                              let uu____79639 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79642 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79642.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79642.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79642.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79642.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79642.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79642.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79642.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79642.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79642.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79642.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79642.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79642.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79642.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79642.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79642.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79642.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79642.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79642.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79642.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79642.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79642.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79642.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79642.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79642.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79642.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79642.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79642.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79642.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79642.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79642.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79642.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79642.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79642.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79642.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79642.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79642.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79642.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79642.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79642.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79642.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79642.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79642.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79639
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79665 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79665)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79587 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79771  ->
                                  match uu___639_79771 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79775 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79775 with
                                       | (uu____79808,xxv) ->
                                           let xx =
                                             let uu____79847 =
                                               let uu____79848 =
                                                 let uu____79854 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79854,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79848
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79847
                                              in
                                           let uu____79857 =
                                             let uu____79858 =
                                               let uu____79866 =
                                                 let uu____79867 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79868 =
                                                   let uu____79879 =
                                                     let uu____79880 =
                                                       let uu____79885 =
                                                         let uu____79886 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79886
                                                          in
                                                       (vapp, uu____79885)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79880
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79879)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79867 uu____79868
                                                  in
                                               (uu____79866,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79858
                                              in
                                           [uu____79857])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79901 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79901 with
                                       | (uu____79934,xxv) ->
                                           let xx =
                                             let uu____79973 =
                                               let uu____79974 =
                                                 let uu____79980 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79980,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79974
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79973
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
                                           let uu____79991 =
                                             let uu____79992 =
                                               let uu____80000 =
                                                 let uu____80001 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80002 =
                                                   let uu____80013 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80013)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80001 uu____80002
                                                  in
                                               (uu____80000,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79992
                                              in
                                           [uu____79991])
                                  | uu____80026 -> []))
                           in
                        let uu____80027 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80027 with
                         | (vars,guards,env',decls1,uu____80052) ->
                             let uu____80065 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80078 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80078, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80082 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80082 with
                                    | (g,ds) ->
                                        let uu____80095 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80095,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80065 with
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
                                  let should_thunk uu____80118 =
                                    let is_type1 t =
                                      let uu____80126 =
                                        let uu____80127 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80127.FStar_Syntax_Syntax.n  in
                                      match uu____80126 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80131 -> true
                                      | uu____80133 -> false  in
                                    let is_squash1 t =
                                      let uu____80142 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80142 with
                                      | (head1,uu____80161) ->
                                          let uu____80186 =
                                            let uu____80187 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80187.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80186 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80192;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80193;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80195;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80196;_};_},uu____80197)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80205 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80210 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80210))
                                       &&
                                       (let uu____80216 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80216))
                                      &&
                                      (let uu____80219 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80219)
                                     in
                                  let uu____80221 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80280 -> (false, vars)  in
                                  (match uu____80221 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80330 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80330 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80366 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80375 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80375
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80386 ->
                                                  let uu____80395 =
                                                    let uu____80403 =
                                                      get_vtok ()  in
                                                    (uu____80403, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80395
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80410 =
                                                let uu____80418 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80418)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80410
                                               in
                                            let uu____80432 =
                                              let vname_decl =
                                                let uu____80440 =
                                                  let uu____80452 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80452,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80440
                                                 in
                                              let uu____80463 =
                                                let env2 =
                                                  let uu___1026_80469 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80469.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80470 =
                                                  let uu____80472 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80472
                                                   in
                                                if uu____80470
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80463 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80489 =
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
                                                        let uu____80515 =
                                                          let uu____80518 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80518
                                                           in
                                                        let uu____80525 =
                                                          let uu____80526 =
                                                            let uu____80529 =
                                                              let uu____80530
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80530
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80534  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80534)
                                                              uu____80529
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80526
                                                           in
                                                        (uu____80515,
                                                          uu____80525)
                                                    | uu____80541 when
                                                        thunked ->
                                                        let uu____80552 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80552
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80567
                                                                 =
                                                                 let uu____80575
                                                                   =
                                                                   let uu____80578
                                                                    =
                                                                    let uu____80581
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80581]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80578
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80575)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80567
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80589
                                                               =
                                                               let uu____80597
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80597,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80589
                                                              in
                                                           let uu____80602 =
                                                             let uu____80605
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80605
                                                              in
                                                           (uu____80602,
                                                             env1))
                                                    | uu____80614 ->
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
                                                          let uu____80638 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80639 =
                                                            let uu____80650 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80650)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80638
                                                            uu____80639
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80660 =
                                                            let uu____80668 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80668,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80660
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
                                                            let uu____80679 =
                                                              let uu____80680
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80680]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80679
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80707 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80708 =
                                                              let uu____80719
                                                                =
                                                                let uu____80720
                                                                  =
                                                                  let uu____80725
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80726
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80725,
                                                                    uu____80726)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80720
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80719)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80707
                                                              uu____80708
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80755 =
                                                          let uu____80758 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80758
                                                           in
                                                        (uu____80755, env1)
                                                     in
                                                  (match uu____80489 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80779 =
                                                         let uu____80782 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80782
                                                           tok_decl
                                                          in
                                                       (uu____80779, env2))
                                               in
                                            (match uu____80432 with
                                             | (decls2,env2) ->
                                                 let uu____80801 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80811 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80811 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80826 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80826, decls)
                                                    in
                                                 (match uu____80801 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80841 =
                                                          let uu____80849 =
                                                            let uu____80850 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80851 =
                                                              let uu____80862
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80862)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80850
                                                              uu____80851
                                                             in
                                                          (uu____80849,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80841
                                                         in
                                                      let freshness =
                                                        let uu____80878 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80878
                                                        then
                                                          let uu____80886 =
                                                            let uu____80887 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80888 =
                                                              let uu____80901
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____80908
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80901,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____80908)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80887
                                                              uu____80888
                                                             in
                                                          let uu____80914 =
                                                            let uu____80917 =
                                                              let uu____80918
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____80918
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____80917]  in
                                                          uu____80886 ::
                                                            uu____80914
                                                        else []  in
                                                      let g =
                                                        let uu____80924 =
                                                          let uu____80927 =
                                                            let uu____80930 =
                                                              let uu____80933
                                                                =
                                                                let uu____80936
                                                                  =
                                                                  let uu____80939
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____80939
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____80936
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____80933
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____80930
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80927
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____80924
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
          let uu____80979 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____80979 with
          | FStar_Pervasives_Native.None  ->
              let uu____80990 = encode_free_var false env x t t_norm []  in
              (match uu____80990 with
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
            let uu____81053 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81053 with
            | (decls,env1) ->
                let uu____81064 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81064
                then
                  let uu____81071 =
                    let uu____81072 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81072  in
                  (uu____81071, env1)
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
             (fun uu____81128  ->
                fun lb  ->
                  match uu____81128 with
                  | (decls,env1) ->
                      let uu____81148 =
                        let uu____81153 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81153
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81148 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81182 = FStar_Syntax_Util.head_and_args t  in
    match uu____81182 with
    | (hd1,args) ->
        let uu____81226 =
          let uu____81227 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81227.FStar_Syntax_Syntax.n  in
        (match uu____81226 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81233,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81257 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81268 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81276 = en  in
    let uu____81277 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81276.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81276.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81276.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81276.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81276.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81276.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81276.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81276.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81276.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81276.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81277
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81307  ->
      fun quals  ->
        match uu____81307 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81412 = FStar_Util.first_N nbinders formals  in
              match uu____81412 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81513  ->
                         fun uu____81514  ->
                           match (uu____81513, uu____81514) with
                           | ((formal,uu____81540),(binder,uu____81542)) ->
                               let uu____81563 =
                                 let uu____81570 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81570)  in
                               FStar_Syntax_Syntax.NT uu____81563) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81584 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81625  ->
                              match uu____81625 with
                              | (x,i) ->
                                  let uu____81644 =
                                    let uu___1139_81645 = x  in
                                    let uu____81646 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81645.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81645.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81646
                                    }  in
                                  (uu____81644, i)))
                       in
                    FStar_All.pipe_right uu____81584
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81670 =
                      let uu____81675 = FStar_Syntax_Subst.compress body  in
                      let uu____81676 =
                        let uu____81677 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81677
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81675
                        uu____81676
                       in
                    uu____81670 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81728 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81728.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81728.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81728.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81728.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81728.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81728.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81728.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81728.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81728.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81728.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81728.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81728.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81728.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81728.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81728.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81728.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81728.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81728.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81728.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81728.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81728.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81728.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81728.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81728.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81728.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81728.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81728.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81728.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81728.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81728.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81728.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81728.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81728.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81728.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81728.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81728.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81728.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81728.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81728.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81728.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81728.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81728.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81800  ->
                       fun uu____81801  ->
                         match (uu____81800, uu____81801) with
                         | ((x,uu____81827),(b,uu____81829)) ->
                             let uu____81850 =
                               let uu____81857 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81857)  in
                             FStar_Syntax_Syntax.NT uu____81850) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81882 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81882
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____81911 ->
                    let uu____81918 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____81918
                | uu____81919 when Prims.op_Negation norm1 ->
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
                | uu____81922 ->
                    let uu____81923 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____81923)
                 in
              let aux t1 e1 =
                let uu____81965 = FStar_Syntax_Util.abs_formals e1  in
                match uu____81965 with
                | (binders,body,lopt) ->
                    let uu____81997 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82013 -> arrow_formals_comp_norm false t1  in
                    (match uu____81997 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82047 =
                           if nformals < nbinders
                           then
                             let uu____82091 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82091 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82175 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82175)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82215 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82215 with
                                | (binders1,body1) ->
                                    let uu____82268 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82268))
                             else
                               (let uu____82281 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82281))
                            in
                         (match uu____82047 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82341 = aux t e  in
              match uu____82341 with
              | (binders,body,comp) ->
                  let uu____82387 =
                    let uu____82398 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82398
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82413 = aux comp1 body1  in
                      match uu____82413 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82387 with
                   | (binders1,body1,comp1) ->
                       let uu____82496 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82496, comp1))
               in
            (try
               (fun uu___1216_82523  ->
                  match () with
                  | () ->
                      let uu____82530 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82530
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82546 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82609  ->
                                   fun lb  ->
                                     match uu____82609 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82664 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82664
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82670 =
                                             let uu____82679 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82679
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82670 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82546 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82820;
                                    FStar_Syntax_Syntax.lbeff = uu____82821;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82823;
                                    FStar_Syntax_Syntax.lbpos = uu____82824;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82848 =
                                     let uu____82855 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82855 with
                                     | (tcenv',uu____82871,e_t) ->
                                         let uu____82877 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82888 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82877 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82905 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82905.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82848 with
                                    | (env',e1,t_norm1) ->
                                        let uu____82915 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____82915 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____82935 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____82935
                                               then
                                                 let uu____82940 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____82943 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____82940 uu____82943
                                               else ());
                                              (let uu____82948 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____82948 with
                                               | (vars,_guards,env'1,binder_decls,uu____82975)
                                                   ->
                                                   let uu____82988 =
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
                                                         let uu____83005 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83005
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83027 =
                                                          let uu____83028 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83029 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83028 fvb
                                                            uu____83029
                                                           in
                                                        (vars, uu____83027))
                                                      in
                                                   (match uu____82988 with
                                                    | (vars1,app) ->
                                                        let uu____83040 =
                                                          let is_logical =
                                                            let uu____83053 =
                                                              let uu____83054
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83054.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83053
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83060 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83064 =
                                                              let uu____83065
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83065
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83064
                                                              (fun lid  ->
                                                                 let uu____83074
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83074
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83075 =
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
                                                          if uu____83075
                                                          then
                                                            let uu____83091 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83092 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83091,
                                                              uu____83092)
                                                          else
                                                            (let uu____83103
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83103))
                                                           in
                                                        (match uu____83040
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83127
                                                                 =
                                                                 let uu____83135
                                                                   =
                                                                   let uu____83136
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83137
                                                                    =
                                                                    let uu____83148
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83148)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83136
                                                                    uu____83137
                                                                    in
                                                                 let uu____83157
                                                                   =
                                                                   let uu____83158
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83158
                                                                    in
                                                                 (uu____83135,
                                                                   uu____83157,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83127
                                                                in
                                                             let uu____83164
                                                               =
                                                               let uu____83167
                                                                 =
                                                                 let uu____83170
                                                                   =
                                                                   let uu____83173
                                                                    =
                                                                    let uu____83176
                                                                    =
                                                                    let uu____83179
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83179
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83176
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83173
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83170
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83167
                                                                in
                                                             (uu____83164,
                                                               env2)))))))
                               | uu____83188 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83248 =
                                   let uu____83254 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83254,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83248  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83260 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83313  ->
                                         fun fvb  ->
                                           match uu____83313 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83368 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83368
                                                  in
                                               let gtok =
                                                 let uu____83372 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83372
                                                  in
                                               let env4 =
                                                 let uu____83375 =
                                                   let uu____83378 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83384  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83384) uu____83378
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83375
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83260 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83504
                                     t_norm uu____83506 =
                                     match (uu____83504, uu____83506) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83536;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83537;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83539;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83540;_})
                                         ->
                                         let uu____83567 =
                                           let uu____83574 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83574 with
                                           | (tcenv',uu____83590,e_t) ->
                                               let uu____83596 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83607 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83596 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83624 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83624.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83567 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83637 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83637
                                                then
                                                  let uu____83642 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83644 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83646 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83642 uu____83644
                                                    uu____83646
                                                else ());
                                               (let uu____83651 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83651 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83678 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83678 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83700 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83700
                                                           then
                                                             let uu____83705
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83707
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83710
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83712
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83705
                                                               uu____83707
                                                               uu____83710
                                                               uu____83712
                                                           else ());
                                                          (let uu____83717 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83717
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83746)
                                                               ->
                                                               let uu____83759
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83772
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83772,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83776
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83776
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83789,
                                                                    decls0))
                                                                  in
                                                               (match uu____83759
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
                                                                    let uu____83810
                                                                    =
                                                                    let uu____83822
                                                                    =
                                                                    let uu____83825
                                                                    =
                                                                    let uu____83828
                                                                    =
                                                                    let uu____83831
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83831
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83828
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83825
                                                                     in
                                                                    (g,
                                                                    uu____83822,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83810
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
                                                                    let uu____83861
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83861
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
                                                                    let uu____83876
                                                                    =
                                                                    let uu____83879
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83879
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83876
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83885
                                                                    =
                                                                    let uu____83888
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83888
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83885
                                                                     in
                                                                    let uu____83893
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83893
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____83909
                                                                    =
                                                                    let uu____83917
                                                                    =
                                                                    let uu____83918
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83919
                                                                    =
                                                                    let uu____83935
                                                                    =
                                                                    let uu____83936
                                                                    =
                                                                    let uu____83941
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____83941)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83936
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83935)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____83918
                                                                    uu____83919
                                                                     in
                                                                    let uu____83955
                                                                    =
                                                                    let uu____83956
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____83956
                                                                     in
                                                                    (uu____83917,
                                                                    uu____83955,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83909
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____83963
                                                                    =
                                                                    let uu____83971
                                                                    =
                                                                    let uu____83972
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83973
                                                                    =
                                                                    let uu____83984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____83984)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83972
                                                                    uu____83973
                                                                     in
                                                                    (uu____83971,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83963
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____83998
                                                                    =
                                                                    let uu____84006
                                                                    =
                                                                    let uu____84007
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84008
                                                                    =
                                                                    let uu____84019
                                                                    =
                                                                    let uu____84020
                                                                    =
                                                                    let uu____84025
                                                                    =
                                                                    let uu____84026
                                                                    =
                                                                    let uu____84029
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84029
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84026
                                                                     in
                                                                    (gsapp,
                                                                    uu____84025)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84020
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84019)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84007
                                                                    uu____84008
                                                                     in
                                                                    (uu____84006,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83998
                                                                     in
                                                                    let uu____84043
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
                                                                    let uu____84055
                                                                    =
                                                                    let uu____84056
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84056
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84055
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84058
                                                                    =
                                                                    let uu____84066
                                                                    =
                                                                    let uu____84067
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84068
                                                                    =
                                                                    let uu____84079
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84079)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84067
                                                                    uu____84068
                                                                     in
                                                                    (uu____84066,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84058
                                                                     in
                                                                    let uu____84092
                                                                    =
                                                                    let uu____84101
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84101
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84116
                                                                    =
                                                                    let uu____84119
                                                                    =
                                                                    let uu____84120
                                                                    =
                                                                    let uu____84128
                                                                    =
                                                                    let uu____84129
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84130
                                                                    =
                                                                    let uu____84141
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84141)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84129
                                                                    uu____84130
                                                                     in
                                                                    (uu____84128,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84120
                                                                     in
                                                                    [uu____84119]
                                                                     in
                                                                    (d3,
                                                                    uu____84116)
                                                                     in
                                                                    match uu____84092
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84043
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84198
                                                                    =
                                                                    let uu____84201
                                                                    =
                                                                    let uu____84204
                                                                    =
                                                                    let uu____84207
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84207
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84204
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84201
                                                                     in
                                                                    let uu____84214
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84198,
                                                                    uu____84214,
                                                                    env02))))))))))
                                      in
                                   let uu____84219 =
                                     let uu____84232 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84295  ->
                                          fun uu____84296  ->
                                            match (uu____84295, uu____84296)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84421 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84421 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84232
                                      in
                                   (match uu____84219 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84488 =
                                          let isDeclFun uu___640_84505 =
                                            match uu___640_84505 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84507 -> true
                                            | uu____84520 -> false  in
                                          let uu____84522 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84522
                                            (fun decls3  ->
                                               let uu____84552 =
                                                 FStar_List.fold_left
                                                   (fun uu____84583  ->
                                                      fun elt  ->
                                                        match uu____84583
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84624 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84624
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84652
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84652
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
                                                                    let uu___1459_84690
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84690.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84690.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84690.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84552 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84722 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84722, elts, rest))
                                           in
                                        (match uu____84488 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84751 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84757  ->
                                        match uu___641_84757 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84760 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84768 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84768)))
                                in
                             if uu____84751
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84790  ->
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
                   let uu____84829 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84829
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84848 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84848, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84904 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84904 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____84910 = encode_sigelt' env se  in
      match uu____84910 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____84922 =
                  let uu____84925 =
                    let uu____84926 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____84926  in
                  [uu____84925]  in
                FStar_All.pipe_right uu____84922
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____84931 ->
                let uu____84932 =
                  let uu____84935 =
                    let uu____84938 =
                      let uu____84939 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____84939  in
                    [uu____84938]  in
                  FStar_All.pipe_right uu____84935
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____84946 =
                  let uu____84949 =
                    let uu____84952 =
                      let uu____84955 =
                        let uu____84956 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____84956  in
                      [uu____84955]  in
                    FStar_All.pipe_right uu____84952
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____84949  in
                FStar_List.append uu____84932 uu____84946
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____84970 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____84970
       then
         let uu____84975 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____84975
       else ());
      (let is_opaque_to_smt t =
         let uu____84987 =
           let uu____84988 = FStar_Syntax_Subst.compress t  in
           uu____84988.FStar_Syntax_Syntax.n  in
         match uu____84987 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____84993)) -> s = "opaque_to_smt"
         | uu____84998 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85007 =
           let uu____85008 = FStar_Syntax_Subst.compress t  in
           uu____85008.FStar_Syntax_Syntax.n  in
         match uu____85007 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85013)) -> s = "uninterpreted_by_smt"
         | uu____85018 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85024 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85030 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85042 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85043 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85044 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85057 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85059 =
             let uu____85061 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85061  in
           if uu____85059
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85090 ->
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
                let uu____85122 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85122 with
                | (formals,uu____85142) ->
                    let arity = FStar_List.length formals  in
                    let uu____85166 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85166 with
                     | (aname,atok,env2) ->
                         let uu____85192 =
                           let uu____85197 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85197 env2
                            in
                         (match uu____85192 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85209 =
                                  let uu____85210 =
                                    let uu____85222 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85242  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85222,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85210
                                   in
                                [uu____85209;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85259 =
                                let aux uu____85305 uu____85306 =
                                  match (uu____85305, uu____85306) with
                                  | ((bv,uu____85350),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85382 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85382 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85405 =
                                             let uu____85408 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85408 :: acc_sorts  in
                                           (env4, uu____85405, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85259 with
                               | (uu____85440,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85456 =
                                       let uu____85464 =
                                         let uu____85465 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85466 =
                                           let uu____85477 =
                                             let uu____85478 =
                                               let uu____85483 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85483)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85478
                                              in
                                           ([[app]], xs_sorts, uu____85477)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85465 uu____85466
                                          in
                                       (uu____85464,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85456
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85498 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85498
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85501 =
                                       let uu____85509 =
                                         let uu____85510 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85511 =
                                           let uu____85522 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85522)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85510 uu____85511
                                          in
                                       (uu____85509,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85501
                                      in
                                   let uu____85535 =
                                     let uu____85538 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85538  in
                                   (env2, uu____85535))))
                 in
              let uu____85547 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85547 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85573,uu____85574)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85575 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85575 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85597,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85604 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85610  ->
                       match uu___642_85610 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85613 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85619 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85622 -> false))
                in
             Prims.op_Negation uu____85604  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85632 =
                let uu____85637 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85637 env fv t quals  in
              match uu____85632 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85651 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85651  in
                  let uu____85654 =
                    let uu____85655 =
                      let uu____85658 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85658
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85655  in
                  (uu____85654, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85668 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85668 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85680 = env  in
                  let uu____85681 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85680.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85680.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85680.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85681;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85680.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85680.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85680.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85680.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85680.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85680.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85680.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85683 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85683 with
                 | (f3,decls) ->
                     let g =
                       let uu____85697 =
                         let uu____85700 =
                           let uu____85701 =
                             let uu____85709 =
                               let uu____85710 =
                                 let uu____85712 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85712
                                  in
                               FStar_Pervasives_Native.Some uu____85710  in
                             let uu____85716 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85709, uu____85716)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85701  in
                         [uu____85700]  in
                       FStar_All.pipe_right uu____85697
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85725) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85739 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85761 =
                        let uu____85764 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85764.FStar_Syntax_Syntax.fv_name  in
                      uu____85761.FStar_Syntax_Syntax.v  in
                    let uu____85765 =
                      let uu____85767 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85767  in
                    if uu____85765
                    then
                      let val_decl =
                        let uu___1629_85799 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85799.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85799.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85799.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85800 = encode_sigelt' env1 val_decl  in
                      match uu____85800 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85739 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85836,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85838;
                           FStar_Syntax_Syntax.lbtyp = uu____85839;
                           FStar_Syntax_Syntax.lbeff = uu____85840;
                           FStar_Syntax_Syntax.lbdef = uu____85841;
                           FStar_Syntax_Syntax.lbattrs = uu____85842;
                           FStar_Syntax_Syntax.lbpos = uu____85843;_}::[]),uu____85844)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85863 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85863 with
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
                  let uu____85901 =
                    let uu____85904 =
                      let uu____85905 =
                        let uu____85913 =
                          let uu____85914 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____85915 =
                            let uu____85926 =
                              let uu____85927 =
                                let uu____85932 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____85932)  in
                              FStar_SMTEncoding_Util.mkEq uu____85927  in
                            ([[b2t_x]], [xx], uu____85926)  in
                          FStar_SMTEncoding_Term.mkForall uu____85914
                            uu____85915
                           in
                        (uu____85913,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85905  in
                    [uu____85904]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85901
                   in
                let uu____85970 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____85970, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____85973,uu____85974) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_85984  ->
                   match uu___643_85984 with
                   | FStar_Syntax_Syntax.Discriminator uu____85986 -> true
                   | uu____85988 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____85990,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86002 =
                      let uu____86004 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86004.FStar_Ident.idText  in
                    uu____86002 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86011  ->
                      match uu___644_86011 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86014 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86017) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86031  ->
                   match uu___645_86031 with
                   | FStar_Syntax_Syntax.Projector uu____86033 -> true
                   | uu____86039 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86043 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86043 with
            | FStar_Pervasives_Native.Some uu____86050 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86052 = se  in
                  let uu____86053 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86053;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86052.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86052.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86052.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86056) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86071) ->
           let uu____86080 = encode_sigelts env ses  in
           (match uu____86080 with
            | (g,env1) ->
                let uu____86091 =
                  FStar_List.fold_left
                    (fun uu____86115  ->
                       fun elt  ->
                         match uu____86115 with
                         | (g',inversions) ->
                             let uu____86143 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86166  ->
                                       match uu___646_86166 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86168;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86169;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86170;_}
                                           -> false
                                       | uu____86177 -> true))
                                in
                             (match uu____86143 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86202 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86202.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86202.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86202.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86091 with
                 | (g',inversions) ->
                     let uu____86221 =
                       FStar_List.fold_left
                         (fun uu____86252  ->
                            fun elt  ->
                              match uu____86252 with
                              | (decls,elts,rest) ->
                                  let uu____86293 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86302  ->
                                            match uu___647_86302 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86304 -> true
                                            | uu____86317 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86293
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86340 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86361  ->
                                               match uu___648_86361 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86363 -> true
                                               | uu____86376 -> false))
                                        in
                                     match uu____86340 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86407 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86407.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86407.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86407.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86221 with
                      | (decls,elts,rest) ->
                          let uu____86433 =
                            let uu____86434 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86441 =
                              let uu____86444 =
                                let uu____86447 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86447  in
                              FStar_List.append elts uu____86444  in
                            FStar_List.append uu____86434 uu____86441  in
                          (uu____86433, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86458,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86471 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86471 with
             | (usubst,uvs) ->
                 let uu____86491 =
                   let uu____86498 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86499 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86500 =
                     let uu____86501 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86501 k  in
                   (uu____86498, uu____86499, uu____86500)  in
                 (match uu____86491 with
                  | (env1,tps1,k1) ->
                      let uu____86514 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86514 with
                       | (tps2,k2) ->
                           let uu____86522 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86522 with
                            | (uu____86538,k3) ->
                                let uu____86560 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86560 with
                                 | (tps3,env_tps,uu____86572,us) ->
                                     let u_k =
                                       let uu____86575 =
                                         let uu____86576 =
                                           FStar_Syntax_Subst.compress k3  in
                                         uu____86576.FStar_Syntax_Syntax.n
                                          in
                                       match uu____86575 with
                                       | FStar_Syntax_Syntax.Tm_type u -> u
                                       | FStar_Syntax_Syntax.Tm_fvar fv when
                                           FStar_Syntax_Syntax.fv_eq_lid fv
                                             FStar_Parser_Const.eqtype_lid
                                           -> FStar_Syntax_Syntax.U_zero
                                       | uu____86581 ->
                                           let uu____86582 =
                                             let uu____86584 =
                                               FStar_Syntax_Print.term_to_string
                                                 k3
                                                in
                                             FStar_Util.format1
                                               "Impossible: Type of inductive is %s"
                                               uu____86584
                                              in
                                           failwith uu____86582
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86600) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86606,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86609) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86617,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | uu____86624 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86637 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86637 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86655 = u_leq_u_k u_tp  in
                                       if uu____86655
                                       then true
                                       else
                                         (let uu____86662 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86662 with
                                          | (formals,uu____86679) ->
                                              let uu____86700 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86700 with
                                               | (uu____86710,uu____86711,uu____86712,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86723 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86723
             then
               let uu____86728 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86728
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86748  ->
                       match uu___649_86748 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86752 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86765 = c  in
                 match uu____86765 with
                 | (name,args,uu____86770,uu____86771,uu____86772) ->
                     let uu____86783 =
                       let uu____86784 =
                         let uu____86796 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86823  ->
                                   match uu____86823 with
                                   | (uu____86832,sort,uu____86834) -> sort))
                            in
                         (name, uu____86796,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86784  in
                     [uu____86783]
               else
                 (let uu____86845 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____86845 c)
                in
             let inversion_axioms tapp vars =
               let uu____86863 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____86871 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____86871 FStar_Option.isNone))
                  in
               if uu____86863
               then []
               else
                 (let uu____86906 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____86906 with
                  | (xxsym,xx) ->
                      let uu____86919 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____86958  ->
                                fun l  ->
                                  match uu____86958 with
                                  | (out,decls) ->
                                      let uu____86978 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____86978 with
                                       | (uu____86989,data_t) ->
                                           let uu____86991 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____86991 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87035 =
                                                    let uu____87036 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87036.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87035 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87039,indices)
                                                      -> indices
                                                  | uu____87065 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87095  ->
                                                            match uu____87095
                                                            with
                                                            | (x,uu____87103)
                                                                ->
                                                                let uu____87108
                                                                  =
                                                                  let uu____87109
                                                                    =
                                                                    let uu____87117
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87117,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87109
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87108)
                                                       env)
                                                   in
                                                let uu____87122 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87122 with
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
                                                                  let uu____87157
                                                                    =
                                                                    let uu____87162
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87162,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87157)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87165 =
                                                         let uu____87166 =
                                                           let uu____87171 =
                                                             let uu____87172
                                                               =
                                                               let uu____87177
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87178
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87177,
                                                                 uu____87178)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87172
                                                              in
                                                           (out, uu____87171)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87166
                                                          in
                                                       (uu____87165,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____86919 with
                       | (data_ax,decls) ->
                           let uu____87193 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87193 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87210 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87210 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87217 =
                                    let uu____87225 =
                                      let uu____87226 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87227 =
                                        let uu____87238 =
                                          let uu____87239 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87241 =
                                            let uu____87244 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87244 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87239 uu____87241
                                           in
                                        let uu____87246 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87238,
                                          uu____87246)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87226 uu____87227
                                       in
                                    let uu____87255 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87225,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87255)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87217
                                   in
                                let uu____87261 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87261)))
                in
             let uu____87268 =
               let uu____87273 =
                 let uu____87274 = FStar_Syntax_Subst.compress k  in
                 uu____87274.FStar_Syntax_Syntax.n  in
               match uu____87273 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87309 -> (tps, k)  in
             match uu____87268 with
             | (formals,res) ->
                 let uu____87316 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87316 with
                  | (formals1,res1) ->
                      let uu____87327 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87327 with
                       | (vars,guards,env',binder_decls,uu____87352) ->
                           let arity = FStar_List.length vars  in
                           let uu____87366 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87366 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87396 =
                                    let uu____87404 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87404)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87396
                                   in
                                let uu____87410 =
                                  let tname_decl =
                                    let uu____87420 =
                                      let uu____87421 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87440 =
                                                  let uu____87442 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87442
                                                   in
                                                let uu____87444 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87440, uu____87444,
                                                  false)))
                                         in
                                      let uu____87448 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87421,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87448, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87420
                                     in
                                  let uu____87456 =
                                    match vars with
                                    | [] ->
                                        let uu____87469 =
                                          let uu____87470 =
                                            let uu____87473 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87479  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87479) uu____87473
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87470
                                           in
                                        ([], uu____87469)
                                    | uu____87486 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87496 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87496
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87512 =
                                            let uu____87520 =
                                              let uu____87521 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87522 =
                                                let uu____87538 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87538)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87521 uu____87522
                                               in
                                            (uu____87520,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87512
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87456 with
                                  | (tok_decls,env2) ->
                                      let uu____87565 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87565
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87410 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87593 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87593 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87615 =
                                                 let uu____87616 =
                                                   let uu____87624 =
                                                     let uu____87625 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87625
                                                      in
                                                   (uu____87624,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87616
                                                  in
                                               [uu____87615]
                                             else []  in
                                           let uu____87633 =
                                             let uu____87636 =
                                               let uu____87639 =
                                                 let uu____87642 =
                                                   let uu____87643 =
                                                     let uu____87651 =
                                                       let uu____87652 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87653 =
                                                         let uu____87664 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87664)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87652
                                                         uu____87653
                                                        in
                                                     (uu____87651,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87643
                                                    in
                                                 [uu____87642]  in
                                               FStar_List.append karr
                                                 uu____87639
                                                in
                                             FStar_All.pipe_right uu____87636
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87633
                                        in
                                     let aux =
                                       let uu____87683 =
                                         let uu____87686 =
                                           inversion_axioms tapp vars  in
                                         let uu____87689 =
                                           let uu____87692 =
                                             let uu____87695 =
                                               let uu____87696 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87696 env2
                                                 tapp vars
                                                in
                                             [uu____87695]  in
                                           FStar_All.pipe_right uu____87692
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87686
                                           uu____87689
                                          in
                                       FStar_List.append kindingAx
                                         uu____87683
                                        in
                                     let g =
                                       let uu____87704 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87704
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87712,uu____87713,uu____87714,uu____87715,uu____87716)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87724,t,uu____87726,n_tps,uu____87728) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87738 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87738 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87786 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87786 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87814 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87814 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____87834 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____87834 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____87913 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____87913,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____87920 =
                                   let uu____87921 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____87921, true)
                                    in
                                 let uu____87929 =
                                   let uu____87936 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____87936
                                    in
                                 FStar_All.pipe_right uu____87920 uu____87929
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
                               let uu____87948 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____87948 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____87960::uu____87961 ->
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
                                            let uu____88010 =
                                              let uu____88011 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88011]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88010
                                             in
                                          let uu____88037 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88038 =
                                            let uu____88049 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88049)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88037 uu____88038
                                      | uu____88076 -> tok_typing  in
                                    let uu____88087 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88087 with
                                     | (vars',guards',env'',decls_formals,uu____88112)
                                         ->
                                         let uu____88125 =
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
                                         (match uu____88125 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88155 ->
                                                    let uu____88164 =
                                                      let uu____88165 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88165
                                                       in
                                                    [uu____88164]
                                                 in
                                              let encode_elim uu____88181 =
                                                let uu____88182 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88182 with
                                                | (head1,args) ->
                                                    let uu____88233 =
                                                      let uu____88234 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88234.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88233 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88246;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88247;_},uu____88248)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88254 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88254
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
                                                                  | uu____88317
                                                                    ->
                                                                    let uu____88318
                                                                    =
                                                                    let uu____88324
                                                                    =
                                                                    let uu____88326
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88326
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88324)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88318
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88349
                                                                    =
                                                                    let uu____88351
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88351
                                                                     in
                                                                    if
                                                                    uu____88349
                                                                    then
                                                                    let uu____88373
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88373]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88376
                                                                =
                                                                let uu____88390
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88447
                                                                     ->
                                                                    fun
                                                                    uu____88448
                                                                     ->
                                                                    match 
                                                                    (uu____88447,
                                                                    uu____88448)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88559
                                                                    =
                                                                    let uu____88567
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88567
                                                                     in
                                                                    (match uu____88559
                                                                    with
                                                                    | 
                                                                    (uu____88581,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88592
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88592
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88597
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88597
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
                                                                  uu____88390
                                                                 in
                                                              (match uu____88376
                                                               with
                                                               | (uu____88618,arg_vars,elim_eqns_or_guards,uu____88621)
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
                                                                    let uu____88648
                                                                    =
                                                                    let uu____88656
                                                                    =
                                                                    let uu____88657
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88658
                                                                    =
                                                                    let uu____88669
                                                                    =
                                                                    let uu____88670
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88670
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88672
                                                                    =
                                                                    let uu____88673
                                                                    =
                                                                    let uu____88678
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88678)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88673
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88669,
                                                                    uu____88672)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88657
                                                                    uu____88658
                                                                     in
                                                                    (uu____88656,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88648
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88693
                                                                    =
                                                                    let uu____88694
                                                                    =
                                                                    let uu____88700
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88700,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88694
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88693
                                                                     in
                                                                    let uu____88703
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88703
                                                                    then
                                                                    let x =
                                                                    let uu____88707
                                                                    =
                                                                    let uu____88713
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88713,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88707
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88718
                                                                    =
                                                                    let uu____88726
                                                                    =
                                                                    let uu____88727
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88728
                                                                    =
                                                                    let uu____88739
                                                                    =
                                                                    let uu____88744
                                                                    =
                                                                    let uu____88747
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88747]
                                                                     in
                                                                    [uu____88744]
                                                                     in
                                                                    let uu____88752
                                                                    =
                                                                    let uu____88753
                                                                    =
                                                                    let uu____88758
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88760
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88758,
                                                                    uu____88760)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88753
                                                                     in
                                                                    (uu____88739,
                                                                    [x],
                                                                    uu____88752)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88727
                                                                    uu____88728
                                                                     in
                                                                    let uu____88781
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88726,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88781)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88718
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88792
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
                                                                    (let uu____88815
                                                                    =
                                                                    let uu____88816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88816
                                                                    dapp1  in
                                                                    [uu____88815])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88792
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88823
                                                                    =
                                                                    let uu____88831
                                                                    =
                                                                    let uu____88832
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88833
                                                                    =
                                                                    let uu____88844
                                                                    =
                                                                    let uu____88845
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88845
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88847
                                                                    =
                                                                    let uu____88848
                                                                    =
                                                                    let uu____88853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88853)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88848
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88844,
                                                                    uu____88847)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88832
                                                                    uu____88833
                                                                     in
                                                                    (uu____88831,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88823)
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
                                                         let uu____88872 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88872
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
                                                                  | uu____88935
                                                                    ->
                                                                    let uu____88936
                                                                    =
                                                                    let uu____88942
                                                                    =
                                                                    let uu____88944
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88944
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88942)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88936
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88967
                                                                    =
                                                                    let uu____88969
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88969
                                                                     in
                                                                    if
                                                                    uu____88967
                                                                    then
                                                                    let uu____88991
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88991]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88994
                                                                =
                                                                let uu____89008
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89065
                                                                     ->
                                                                    fun
                                                                    uu____89066
                                                                     ->
                                                                    match 
                                                                    (uu____89065,
                                                                    uu____89066)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89177
                                                                    =
                                                                    let uu____89185
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89185
                                                                     in
                                                                    (match uu____89177
                                                                    with
                                                                    | 
                                                                    (uu____89199,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89210
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89210
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89215
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89215
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
                                                                  uu____89008
                                                                 in
                                                              (match uu____88994
                                                               with
                                                               | (uu____89236,arg_vars,elim_eqns_or_guards,uu____89239)
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
                                                                    let uu____89266
                                                                    =
                                                                    let uu____89274
                                                                    =
                                                                    let uu____89275
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89276
                                                                    =
                                                                    let uu____89287
                                                                    =
                                                                    let uu____89288
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89288
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89290
                                                                    =
                                                                    let uu____89291
                                                                    =
                                                                    let uu____89296
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89296)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89291
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89287,
                                                                    uu____89290)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89275
                                                                    uu____89276
                                                                     in
                                                                    (uu____89274,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89266
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89311
                                                                    =
                                                                    let uu____89312
                                                                    =
                                                                    let uu____89318
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89318,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89312
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89311
                                                                     in
                                                                    let uu____89321
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89321
                                                                    then
                                                                    let x =
                                                                    let uu____89325
                                                                    =
                                                                    let uu____89331
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89331,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89325
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89336
                                                                    =
                                                                    let uu____89344
                                                                    =
                                                                    let uu____89345
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89346
                                                                    =
                                                                    let uu____89357
                                                                    =
                                                                    let uu____89362
                                                                    =
                                                                    let uu____89365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89365]
                                                                     in
                                                                    [uu____89362]
                                                                     in
                                                                    let uu____89370
                                                                    =
                                                                    let uu____89371
                                                                    =
                                                                    let uu____89376
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89378
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89376,
                                                                    uu____89378)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89371
                                                                     in
                                                                    (uu____89357,
                                                                    [x],
                                                                    uu____89370)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89345
                                                                    uu____89346
                                                                     in
                                                                    let uu____89399
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89344,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89399)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89336
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89410
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
                                                                    (let uu____89433
                                                                    =
                                                                    let uu____89434
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89434
                                                                    dapp1  in
                                                                    [uu____89433])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89410
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89441
                                                                    =
                                                                    let uu____89449
                                                                    =
                                                                    let uu____89450
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89451
                                                                    =
                                                                    let uu____89462
                                                                    =
                                                                    let uu____89463
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89463
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89465
                                                                    =
                                                                    let uu____89466
                                                                    =
                                                                    let uu____89471
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89471)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89466
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89462,
                                                                    uu____89465)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89450
                                                                    uu____89451
                                                                     in
                                                                    (uu____89449,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89441)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89488 ->
                                                         ((let uu____89490 =
                                                             let uu____89496
                                                               =
                                                               let uu____89498
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89500
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89498
                                                                 uu____89500
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89496)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89490);
                                                          ([], [])))
                                                 in
                                              let uu____89508 =
                                                encode_elim ()  in
                                              (match uu____89508 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89534 =
                                                       let uu____89537 =
                                                         let uu____89540 =
                                                           let uu____89543 =
                                                             let uu____89546
                                                               =
                                                               let uu____89549
                                                                 =
                                                                 let uu____89552
                                                                   =
                                                                   let uu____89553
                                                                    =
                                                                    let uu____89565
                                                                    =
                                                                    let uu____89566
                                                                    =
                                                                    let uu____89568
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89568
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89566
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89565)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89553
                                                                    in
                                                                 [uu____89552]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89549
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89546
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89579 =
                                                             let uu____89582
                                                               =
                                                               let uu____89585
                                                                 =
                                                                 let uu____89588
                                                                   =
                                                                   let uu____89591
                                                                    =
                                                                    let uu____89594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89599
                                                                    =
                                                                    let uu____89602
                                                                    =
                                                                    let uu____89603
                                                                    =
                                                                    let uu____89611
                                                                    =
                                                                    let uu____89612
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89613
                                                                    =
                                                                    let uu____89624
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89624)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89612
                                                                    uu____89613
                                                                     in
                                                                    (uu____89611,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89603
                                                                     in
                                                                    let uu____89637
                                                                    =
                                                                    let uu____89640
                                                                    =
                                                                    let uu____89641
                                                                    =
                                                                    let uu____89649
                                                                    =
                                                                    let uu____89650
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89651
                                                                    =
                                                                    let uu____89662
                                                                    =
                                                                    let uu____89663
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89663
                                                                    vars'  in
                                                                    let uu____89665
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89662,
                                                                    uu____89665)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89650
                                                                    uu____89651
                                                                     in
                                                                    (uu____89649,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89641
                                                                     in
                                                                    [uu____89640]
                                                                     in
                                                                    uu____89602
                                                                    ::
                                                                    uu____89637
                                                                     in
                                                                    uu____89594
                                                                    ::
                                                                    uu____89599
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89591
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89588
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89585
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89582
                                                              in
                                                           FStar_List.append
                                                             uu____89543
                                                             uu____89579
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89540
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89537
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89534
                                                      in
                                                   let uu____89682 =
                                                     let uu____89683 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89683 g
                                                      in
                                                   (uu____89682, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89717  ->
              fun se  ->
                match uu____89717 with
                | (g,env1) ->
                    let uu____89737 = encode_sigelt env1 se  in
                    (match uu____89737 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89805 =
        match uu____89805 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____89842 ->
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
                 ((let uu____89850 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____89850
                   then
                     let uu____89855 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____89857 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____89859 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____89855 uu____89857 uu____89859
                   else ());
                  (let uu____89864 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____89864 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____89882 =
                         let uu____89890 =
                           let uu____89892 =
                             let uu____89894 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____89894
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____89892  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____89890
                          in
                       (match uu____89882 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____89914 = FStar_Options.log_queries ()
                                 in
                              if uu____89914
                              then
                                let uu____89917 =
                                  let uu____89919 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____89921 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____89923 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____89919 uu____89921 uu____89923
                                   in
                                FStar_Pervasives_Native.Some uu____89917
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____89939 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____89949 =
                                let uu____89952 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____89952  in
                              FStar_List.append uu____89939 uu____89949  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____89964,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____89984 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____89984 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90005 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90005 with | (uu____90032,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90085  ->
              match uu____90085 with
              | (l,uu____90094,uu____90095) ->
                  let uu____90098 =
                    let uu____90110 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90110, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90098))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90143  ->
              match uu____90143 with
              | (l,uu____90154,uu____90155) ->
                  let uu____90158 =
                    let uu____90159 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90162  -> FStar_SMTEncoding_Term.Echo _90162)
                      uu____90159
                     in
                  let uu____90163 =
                    let uu____90166 =
                      let uu____90167 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90167  in
                    [uu____90166]  in
                  uu____90158 :: uu____90163))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90196 =
      let uu____90199 =
        let uu____90200 = FStar_Util.psmap_empty ()  in
        let uu____90215 =
          let uu____90224 = FStar_Util.psmap_empty ()  in (uu____90224, [])
           in
        let uu____90231 =
          let uu____90233 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90233 FStar_Ident.string_of_lid  in
        let uu____90235 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90200;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90215;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90231;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90235
        }  in
      [uu____90199]  in
    FStar_ST.op_Colon_Equals last_env uu____90196
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90279 = FStar_ST.op_Bang last_env  in
      match uu____90279 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90307 ->
          let uu___2166_90310 = e  in
          let uu____90311 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2166_90310.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2166_90310.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2166_90310.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2166_90310.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2166_90310.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2166_90310.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2166_90310.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90311;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2166_90310.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2166_90310.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90319 = FStar_ST.op_Bang last_env  in
    match uu____90319 with
    | [] -> failwith "Empty env stack"
    | uu____90346::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90378  ->
    let uu____90379 = FStar_ST.op_Bang last_env  in
    match uu____90379 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90439  ->
    let uu____90440 = FStar_ST.op_Bang last_env  in
    match uu____90440 with
    | [] -> failwith "Popping an empty stack"
    | uu____90467::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90504  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90557  ->
         let uu____90558 = snapshot_env ()  in
         match uu____90558 with
         | (env_depth,()) ->
             let uu____90580 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90580 with
              | (varops_depth,()) ->
                  let uu____90602 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90602 with
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
        (fun uu____90660  ->
           let uu____90661 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90661 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90756 = snapshot msg  in () 
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
        | (uu____90802::uu____90803,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2227_90811 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2227_90811.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2227_90811.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2227_90811.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90812 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2233_90839 = elt  in
        let uu____90840 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2233_90839.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2233_90839.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____90840;
          FStar_SMTEncoding_Term.a_names =
            (uu___2233_90839.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____90860 =
        let uu____90863 =
          let uu____90864 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____90864  in
        let uu____90865 = open_fact_db_tags env  in uu____90863 ::
          uu____90865
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____90860
  
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
      let uu____90892 = encode_sigelt env se  in
      match uu____90892 with
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
                (let uu____90938 =
                   let uu____90941 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____90941
                    in
                 match uu____90938 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____90956 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____90956
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____90986 = FStar_Options.log_queries ()  in
        if uu____90986
        then
          let uu____90991 =
            let uu____90992 =
              let uu____90994 =
                let uu____90996 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____90996 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____90994  in
            FStar_SMTEncoding_Term.Caption uu____90992  in
          uu____90991 :: decls
        else decls  in
      (let uu____91015 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91015
       then
         let uu____91018 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91018
       else ());
      (let env =
         let uu____91024 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91024 tcenv  in
       let uu____91025 = encode_top_level_facts env se  in
       match uu____91025 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91039 =
               let uu____91042 =
                 let uu____91045 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91045
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91042  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91039)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91078 = FStar_Options.log_queries ()  in
          if uu____91078
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2271_91098 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2271_91098.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2271_91098.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2271_91098.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2271_91098.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2271_91098.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2271_91098.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2271_91098.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2271_91098.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2271_91098.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2271_91098.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91103 =
             let uu____91106 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91106
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91103  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91126 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91126
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
          (let uu____91150 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91150
           then
             let uu____91153 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91153
           else ());
          (let env =
             let uu____91161 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91161
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91200  ->
                     fun se  ->
                       match uu____91200 with
                       | (g,env2) ->
                           let uu____91220 = encode_top_level_facts env2 se
                              in
                           (match uu____91220 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91243 =
             encode_signature
               (let uu___2294_91252 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2294_91252.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2294_91252.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2294_91252.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2294_91252.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2294_91252.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2294_91252.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2294_91252.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2294_91252.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2294_91252.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2294_91252.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91243 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91268 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91268
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91274 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91274))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91302  ->
        match uu____91302 with
        | (decls,fvbs) ->
            ((let uu____91316 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91316
              then ()
              else
                (let uu____91321 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91321
                 then
                   let uu____91324 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91324
                 else ()));
             (let env =
                let uu____91332 = get_env name tcenv  in
                FStar_All.pipe_right uu____91332
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91334 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91334
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91348 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91348
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
        (let uu____91410 =
           let uu____91412 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91412.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91410);
        (let env =
           let uu____91414 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91414 tcenv  in
         let uu____91415 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91454 = aux rest  in
                 (match uu____91454 with
                  | (out,rest1) ->
                      let t =
                        let uu____91482 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91482 with
                        | FStar_Pervasives_Native.Some uu____91485 ->
                            let uu____91486 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91486
                              x.FStar_Syntax_Syntax.sort
                        | uu____91487 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91491 =
                        let uu____91494 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2335_91497 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2335_91497.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2335_91497.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91494 :: out  in
                      (uu____91491, rest1))
             | uu____91502 -> ([], bindings)  in
           let uu____91509 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91509 with
           | (closing,bindings) ->
               let uu____91536 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91536, bindings)
            in
         match uu____91415 with
         | (q1,bindings) ->
             let uu____91567 = encode_env_bindings env bindings  in
             (match uu____91567 with
              | (env_decls,env1) ->
                  ((let uu____91589 =
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
                    if uu____91589
                    then
                      let uu____91596 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91596
                    else ());
                   (let uu____91601 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91601 with
                    | (phi,qdecls) ->
                        let uu____91622 =
                          let uu____91627 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91627 phi
                           in
                        (match uu____91622 with
                         | (labels,phi1) ->
                             let uu____91644 = encode_labels labels  in
                             (match uu____91644 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91680 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91680
                                    then
                                      let uu____91685 =
                                        let uu____91686 =
                                          let uu____91688 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91688
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91686
                                         in
                                      [uu____91685]
                                    else []  in
                                  let query_prelude =
                                    let uu____91696 =
                                      let uu____91697 =
                                        let uu____91698 =
                                          let uu____91701 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91708 =
                                            let uu____91711 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91711
                                             in
                                          FStar_List.append uu____91701
                                            uu____91708
                                           in
                                        FStar_List.append env_decls
                                          uu____91698
                                         in
                                      FStar_All.pipe_right uu____91697
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91696
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91721 =
                                      let uu____91729 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91730 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91729,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91730)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91721
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
  