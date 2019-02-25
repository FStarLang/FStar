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
  let uu____72774 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____72774 with
  | (asym,a) ->
      let uu____72785 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____72785 with
       | (xsym,x) ->
           let uu____72796 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____72796 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____72874 =
                      let uu____72886 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____72886, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____72874  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____72906 =
                      let uu____72914 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____72914)  in
                    FStar_SMTEncoding_Util.mkApp uu____72906  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____72933 =
                    let uu____72936 =
                      let uu____72939 =
                        let uu____72942 =
                          let uu____72943 =
                            let uu____72951 =
                              let uu____72952 =
                                let uu____72963 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____72963)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____72952
                               in
                            (uu____72951, FStar_Pervasives_Native.None,
                              (Prims.op_Hat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____72943  in
                        let uu____72975 =
                          let uu____72978 =
                            let uu____72979 =
                              let uu____72987 =
                                let uu____72988 =
                                  let uu____72999 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____72999)  in
                                FStar_SMTEncoding_Term.mkForall rng
                                  uu____72988
                                 in
                              (uu____72987,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.op_Hat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____72979  in
                          [uu____72978]  in
                        uu____72942 :: uu____72975  in
                      xtok_decl :: uu____72939  in
                    xname_decl :: uu____72936  in
                  (xtok1, (FStar_List.length vars), uu____72933)  in
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
                  let uu____73169 =
                    let uu____73190 =
                      let uu____73209 =
                        let uu____73210 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____73210
                         in
                      quant axy uu____73209  in
                    (FStar_Parser_Const.op_Eq, uu____73190)  in
                  let uu____73227 =
                    let uu____73250 =
                      let uu____73271 =
                        let uu____73290 =
                          let uu____73291 =
                            let uu____73292 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____73292  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____73291
                           in
                        quant axy uu____73290  in
                      (FStar_Parser_Const.op_notEq, uu____73271)  in
                    let uu____73309 =
                      let uu____73332 =
                        let uu____73353 =
                          let uu____73372 =
                            let uu____73373 =
                              let uu____73374 =
                                let uu____73379 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____73380 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____73379, uu____73380)  in
                              FStar_SMTEncoding_Util.mkAnd uu____73374  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____73373
                             in
                          quant xy uu____73372  in
                        (FStar_Parser_Const.op_And, uu____73353)  in
                      let uu____73397 =
                        let uu____73420 =
                          let uu____73441 =
                            let uu____73460 =
                              let uu____73461 =
                                let uu____73462 =
                                  let uu____73467 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____73468 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____73467, uu____73468)  in
                                FStar_SMTEncoding_Util.mkOr uu____73462  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____73461
                               in
                            quant xy uu____73460  in
                          (FStar_Parser_Const.op_Or, uu____73441)  in
                        let uu____73485 =
                          let uu____73508 =
                            let uu____73529 =
                              let uu____73548 =
                                let uu____73549 =
                                  let uu____73550 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____73550
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____73549
                                 in
                              quant qx uu____73548  in
                            (FStar_Parser_Const.op_Negation, uu____73529)  in
                          let uu____73567 =
                            let uu____73590 =
                              let uu____73611 =
                                let uu____73630 =
                                  let uu____73631 =
                                    let uu____73632 =
                                      let uu____73637 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____73638 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____73637, uu____73638)  in
                                    FStar_SMTEncoding_Util.mkLT uu____73632
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____73631
                                   in
                                quant xy uu____73630  in
                              (FStar_Parser_Const.op_LT, uu____73611)  in
                            let uu____73655 =
                              let uu____73678 =
                                let uu____73699 =
                                  let uu____73718 =
                                    let uu____73719 =
                                      let uu____73720 =
                                        let uu____73725 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____73726 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____73725, uu____73726)  in
                                      FStar_SMTEncoding_Util.mkLTE
                                        uu____73720
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____73719
                                     in
                                  quant xy uu____73718  in
                                (FStar_Parser_Const.op_LTE, uu____73699)  in
                              let uu____73743 =
                                let uu____73766 =
                                  let uu____73787 =
                                    let uu____73806 =
                                      let uu____73807 =
                                        let uu____73808 =
                                          let uu____73813 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____73814 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____73813, uu____73814)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____73808
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____73807
                                       in
                                    quant xy uu____73806  in
                                  (FStar_Parser_Const.op_GT, uu____73787)  in
                                let uu____73831 =
                                  let uu____73854 =
                                    let uu____73875 =
                                      let uu____73894 =
                                        let uu____73895 =
                                          let uu____73896 =
                                            let uu____73901 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____73902 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____73901, uu____73902)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____73896
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____73895
                                         in
                                      quant xy uu____73894  in
                                    (FStar_Parser_Const.op_GTE, uu____73875)
                                     in
                                  let uu____73919 =
                                    let uu____73942 =
                                      let uu____73963 =
                                        let uu____73982 =
                                          let uu____73983 =
                                            let uu____73984 =
                                              let uu____73989 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____73990 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____73989, uu____73990)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____73984
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____73983
                                           in
                                        quant xy uu____73982  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____73963)
                                       in
                                    let uu____74007 =
                                      let uu____74030 =
                                        let uu____74051 =
                                          let uu____74070 =
                                            let uu____74071 =
                                              let uu____74072 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____74072
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____74071
                                             in
                                          quant qx uu____74070  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____74051)
                                         in
                                      let uu____74089 =
                                        let uu____74112 =
                                          let uu____74133 =
                                            let uu____74152 =
                                              let uu____74153 =
                                                let uu____74154 =
                                                  let uu____74159 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____74160 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____74159, uu____74160)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____74154
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____74153
                                               in
                                            quant xy uu____74152  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____74133)
                                           in
                                        let uu____74177 =
                                          let uu____74200 =
                                            let uu____74221 =
                                              let uu____74240 =
                                                let uu____74241 =
                                                  let uu____74242 =
                                                    let uu____74247 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____74248 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____74247,
                                                      uu____74248)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____74242
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____74241
                                                 in
                                              quant xy uu____74240  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____74221)
                                             in
                                          let uu____74265 =
                                            let uu____74288 =
                                              let uu____74309 =
                                                let uu____74328 =
                                                  let uu____74329 =
                                                    let uu____74330 =
                                                      let uu____74335 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____74336 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____74335,
                                                        uu____74336)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____74330
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____74329
                                                   in
                                                quant xy uu____74328  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____74309)
                                               in
                                            let uu____74353 =
                                              let uu____74376 =
                                                let uu____74397 =
                                                  let uu____74416 =
                                                    let uu____74417 =
                                                      let uu____74418 =
                                                        let uu____74423 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____74424 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____74423,
                                                          uu____74424)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____74418
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____74417
                                                     in
                                                  quant xy uu____74416  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____74397)
                                                 in
                                              let uu____74441 =
                                                let uu____74464 =
                                                  let uu____74485 =
                                                    let uu____74504 =
                                                      let uu____74505 =
                                                        let uu____74506 =
                                                          let uu____74511 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____74512 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____74511,
                                                            uu____74512)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____74506
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____74505
                                                       in
                                                    quant xy uu____74504  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____74485)
                                                   in
                                                let uu____74529 =
                                                  let uu____74552 =
                                                    let uu____74573 =
                                                      let uu____74592 =
                                                        let uu____74593 =
                                                          let uu____74594 =
                                                            let uu____74599 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____74600 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____74599,
                                                              uu____74600)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____74594
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____74593
                                                         in
                                                      quant xy uu____74592
                                                       in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____74573)
                                                     in
                                                  let uu____74617 =
                                                    let uu____74640 =
                                                      let uu____74661 =
                                                        let uu____74680 =
                                                          let uu____74681 =
                                                            let uu____74682 =
                                                              let uu____74687
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____74688
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____74687,
                                                                uu____74688)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____74682
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____74681
                                                           in
                                                        quant xy uu____74680
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____74661)
                                                       in
                                                    let uu____74705 =
                                                      let uu____74728 =
                                                        let uu____74749 =
                                                          let uu____74768 =
                                                            let uu____74769 =
                                                              let uu____74770
                                                                =
                                                                let uu____74775
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____74776
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____74775,
                                                                  uu____74776)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____74770
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____74769
                                                             in
                                                          quant xy
                                                            uu____74768
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____74749)
                                                         in
                                                      let uu____74793 =
                                                        let uu____74816 =
                                                          let uu____74837 =
                                                            let uu____74856 =
                                                              let uu____74857
                                                                =
                                                                let uu____74858
                                                                  =
                                                                  let uu____74863
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____74864
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____74863,
                                                                    uu____74864)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____74858
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____74857
                                                               in
                                                            quant xy
                                                              uu____74856
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____74837)
                                                           in
                                                        let uu____74881 =
                                                          let uu____74904 =
                                                            let uu____74925 =
                                                              let uu____74944
                                                                =
                                                                let uu____74945
                                                                  =
                                                                  let uu____74946
                                                                    =
                                                                    let uu____74951
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____74952
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____74951,
                                                                    uu____74952)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____74946
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____74945
                                                                 in
                                                              quant xy
                                                                uu____74944
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____74925)
                                                             in
                                                          let uu____74969 =
                                                            let uu____74992 =
                                                              let uu____75013
                                                                =
                                                                let uu____75032
                                                                  =
                                                                  let uu____75033
                                                                    =
                                                                    let uu____75034
                                                                    =
                                                                    let uu____75039
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75040
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75039,
                                                                    uu____75040)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____75034
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75033
                                                                   in
                                                                quant xy
                                                                  uu____75032
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____75013)
                                                               in
                                                            let uu____75057 =
                                                              let uu____75080
                                                                =
                                                                let uu____75101
                                                                  =
                                                                  let uu____75120
                                                                    =
                                                                    let uu____75121
                                                                    =
                                                                    let uu____75122
                                                                    =
                                                                    let uu____75127
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____75128
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____75127,
                                                                    uu____75128)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____75122
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75121
                                                                     in
                                                                  quant xy
                                                                    uu____75120
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____75101)
                                                                 in
                                                              let uu____75145
                                                                =
                                                                let uu____75168
                                                                  =
                                                                  let uu____75189
                                                                    =
                                                                    let uu____75208
                                                                    =
                                                                    let uu____75209
                                                                    =
                                                                    let uu____75210
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____75210
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____75209
                                                                     in
                                                                    quant qx
                                                                    uu____75208
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____75189)
                                                                   in
                                                                [uu____75168]
                                                                 in
                                                              uu____75080 ::
                                                                uu____75145
                                                               in
                                                            uu____74992 ::
                                                              uu____75057
                                                             in
                                                          uu____74904 ::
                                                            uu____74969
                                                           in
                                                        uu____74816 ::
                                                          uu____74881
                                                         in
                                                      uu____74728 ::
                                                        uu____74793
                                                       in
                                                    uu____74640 ::
                                                      uu____74705
                                                     in
                                                  uu____74552 :: uu____74617
                                                   in
                                                uu____74464 :: uu____74529
                                                 in
                                              uu____74376 :: uu____74441  in
                                            uu____74288 :: uu____74353  in
                                          uu____74200 :: uu____74265  in
                                        uu____74112 :: uu____74177  in
                                      uu____74030 :: uu____74089  in
                                    uu____73942 :: uu____74007  in
                                  uu____73854 :: uu____73919  in
                                uu____73766 :: uu____73831  in
                              uu____73678 :: uu____73743  in
                            uu____73590 :: uu____73655  in
                          uu____73508 :: uu____73567  in
                        uu____73420 :: uu____73485  in
                      uu____73332 :: uu____73397  in
                    uu____73250 :: uu____73309  in
                  uu____73169 :: uu____73227  in
                let mk1 l v1 =
                  let uu____75749 =
                    let uu____75761 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____75851  ->
                              match uu____75851 with
                              | (l',uu____75872) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____75761
                      (FStar_Option.map
                         (fun uu____75971  ->
                            match uu____75971 with
                            | (uu____75999,b) ->
                                let uu____76033 = FStar_Ident.range_of_lid l
                                   in
                                b uu____76033 v1))
                     in
                  FStar_All.pipe_right uu____75749 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____76116  ->
                          match uu____76116 with
                          | (l',uu____76137) -> FStar_Ident.lid_equals l l'))
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
          let uu____76211 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____76211 with
          | (xxsym,xx) ->
              let uu____76222 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____76222 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____76238 =
                     let uu____76246 =
                       let uu____76247 =
                         let uu____76258 =
                           let uu____76259 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____76269 =
                             let uu____76280 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____76280 :: vars  in
                           uu____76259 :: uu____76269  in
                         let uu____76306 =
                           let uu____76307 =
                             let uu____76312 =
                               let uu____76313 =
                                 let uu____76318 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____76318)  in
                               FStar_SMTEncoding_Util.mkEq uu____76313  in
                             (xx_has_type, uu____76312)  in
                           FStar_SMTEncoding_Util.mkImp uu____76307  in
                         ([[xx_has_type]], uu____76258, uu____76306)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____76247  in
                     let uu____76331 =
                       let uu____76333 =
                         let uu____76335 =
                           let uu____76337 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____76337  in
                         Prims.op_Hat module_name uu____76335  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____76333
                        in
                     (uu____76246,
                       (FStar_Pervasives_Native.Some "pretyping"),
                       uu____76331)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____76238)
  
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
    let uu____76393 =
      let uu____76395 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____76395  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____76393  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____76417 =
      let uu____76418 =
        let uu____76426 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____76426, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76418  in
    let uu____76431 =
      let uu____76434 =
        let uu____76435 =
          let uu____76443 =
            let uu____76444 =
              let uu____76455 =
                let uu____76456 =
                  let uu____76461 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____76461)  in
                FStar_SMTEncoding_Util.mkImp uu____76456  in
              ([[typing_pred]], [xx], uu____76455)  in
            let uu____76486 =
              let uu____76501 = FStar_TypeChecker_Env.get_range env  in
              let uu____76502 = mkForall_fuel1 env  in
              uu____76502 uu____76501  in
            uu____76486 uu____76444  in
          (uu____76443, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76435  in
      [uu____76434]  in
    uu____76417 :: uu____76431  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____76549 =
      let uu____76550 =
        let uu____76558 =
          let uu____76559 = FStar_TypeChecker_Env.get_range env  in
          let uu____76560 =
            let uu____76571 =
              let uu____76576 =
                let uu____76579 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____76579]  in
              [uu____76576]  in
            let uu____76584 =
              let uu____76585 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76585 tt  in
            (uu____76571, [bb], uu____76584)  in
          FStar_SMTEncoding_Term.mkForall uu____76559 uu____76560  in
        (uu____76558, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76550  in
    let uu____76610 =
      let uu____76613 =
        let uu____76614 =
          let uu____76622 =
            let uu____76623 =
              let uu____76634 =
                let uu____76635 =
                  let uu____76640 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____76640)  in
                FStar_SMTEncoding_Util.mkImp uu____76635  in
              ([[typing_pred]], [xx], uu____76634)  in
            let uu____76667 =
              let uu____76682 = FStar_TypeChecker_Env.get_range env  in
              let uu____76683 = mkForall_fuel1 env  in
              uu____76683 uu____76682  in
            uu____76667 uu____76623  in
          (uu____76622, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76614  in
      [uu____76613]  in
    uu____76549 :: uu____76610  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____76726 =
        let uu____76727 =
          let uu____76733 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____76733, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____76727  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____76726  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____76747 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____76747  in
    let uu____76752 =
      let uu____76753 =
        let uu____76761 =
          let uu____76762 = FStar_TypeChecker_Env.get_range env  in
          let uu____76763 =
            let uu____76774 =
              let uu____76779 =
                let uu____76782 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____76782]  in
              [uu____76779]  in
            let uu____76787 =
              let uu____76788 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____76788 tt  in
            (uu____76774, [bb], uu____76787)  in
          FStar_SMTEncoding_Term.mkForall uu____76762 uu____76763  in
        (uu____76761, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____76753  in
    let uu____76813 =
      let uu____76816 =
        let uu____76817 =
          let uu____76825 =
            let uu____76826 =
              let uu____76837 =
                let uu____76838 =
                  let uu____76843 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____76843)  in
                FStar_SMTEncoding_Util.mkImp uu____76838  in
              ([[typing_pred]], [xx], uu____76837)  in
            let uu____76870 =
              let uu____76885 = FStar_TypeChecker_Env.get_range env  in
              let uu____76886 = mkForall_fuel1 env  in
              uu____76886 uu____76885  in
            uu____76870 uu____76826  in
          (uu____76825, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____76817  in
      let uu____76908 =
        let uu____76911 =
          let uu____76912 =
            let uu____76920 =
              let uu____76921 =
                let uu____76932 =
                  let uu____76933 =
                    let uu____76938 =
                      let uu____76939 =
                        let uu____76942 =
                          let uu____76945 =
                            let uu____76948 =
                              let uu____76949 =
                                let uu____76954 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____76955 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____76954, uu____76955)  in
                              FStar_SMTEncoding_Util.mkGT uu____76949  in
                            let uu____76957 =
                              let uu____76960 =
                                let uu____76961 =
                                  let uu____76966 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____76967 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____76966, uu____76967)  in
                                FStar_SMTEncoding_Util.mkGTE uu____76961  in
                              let uu____76969 =
                                let uu____76972 =
                                  let uu____76973 =
                                    let uu____76978 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____76979 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____76978, uu____76979)  in
                                  FStar_SMTEncoding_Util.mkLT uu____76973  in
                                [uu____76972]  in
                              uu____76960 :: uu____76969  in
                            uu____76948 :: uu____76957  in
                          typing_pred_y :: uu____76945  in
                        typing_pred :: uu____76942  in
                      FStar_SMTEncoding_Util.mk_and_l uu____76939  in
                    (uu____76938, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____76933  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____76932)
                 in
              let uu____77012 =
                let uu____77027 = FStar_TypeChecker_Env.get_range env  in
                let uu____77028 = mkForall_fuel1 env  in
                uu____77028 uu____77027  in
              uu____77012 uu____76921  in
            (uu____76920,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____76912  in
        [uu____76911]  in
      uu____76816 :: uu____76908  in
    uu____76752 :: uu____76813  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____77071 =
        let uu____77072 =
          let uu____77078 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____77078, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____77072  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____77071  in
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
      let uu____77094 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____77094  in
    let uu____77099 =
      let uu____77100 =
        let uu____77108 =
          let uu____77109 = FStar_TypeChecker_Env.get_range env  in
          let uu____77110 =
            let uu____77121 =
              let uu____77126 =
                let uu____77129 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____77129]  in
              [uu____77126]  in
            let uu____77134 =
              let uu____77135 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77135 tt  in
            (uu____77121, [bb], uu____77134)  in
          FStar_SMTEncoding_Term.mkForall uu____77109 uu____77110  in
        (uu____77108, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77100  in
    let uu____77160 =
      let uu____77163 =
        let uu____77164 =
          let uu____77172 =
            let uu____77173 =
              let uu____77184 =
                let uu____77185 =
                  let uu____77190 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____77190)  in
                FStar_SMTEncoding_Util.mkImp uu____77185  in
              ([[typing_pred]], [xx], uu____77184)  in
            let uu____77217 =
              let uu____77232 = FStar_TypeChecker_Env.get_range env  in
              let uu____77233 = mkForall_fuel1 env  in
              uu____77233 uu____77232  in
            uu____77217 uu____77173  in
          (uu____77172, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77164  in
      let uu____77255 =
        let uu____77258 =
          let uu____77259 =
            let uu____77267 =
              let uu____77268 =
                let uu____77279 =
                  let uu____77280 =
                    let uu____77285 =
                      let uu____77286 =
                        let uu____77289 =
                          let uu____77292 =
                            let uu____77295 =
                              let uu____77296 =
                                let uu____77301 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____77302 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____77301, uu____77302)  in
                              FStar_SMTEncoding_Util.mkGT uu____77296  in
                            let uu____77304 =
                              let uu____77307 =
                                let uu____77308 =
                                  let uu____77313 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____77314 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____77313, uu____77314)  in
                                FStar_SMTEncoding_Util.mkGTE uu____77308  in
                              let uu____77316 =
                                let uu____77319 =
                                  let uu____77320 =
                                    let uu____77325 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____77326 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____77325, uu____77326)  in
                                  FStar_SMTEncoding_Util.mkLT uu____77320  in
                                [uu____77319]  in
                              uu____77307 :: uu____77316  in
                            uu____77295 :: uu____77304  in
                          typing_pred_y :: uu____77292  in
                        typing_pred :: uu____77289  in
                      FStar_SMTEncoding_Util.mk_and_l uu____77286  in
                    (uu____77285, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____77280  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____77279)
                 in
              let uu____77359 =
                let uu____77374 = FStar_TypeChecker_Env.get_range env  in
                let uu____77375 = mkForall_fuel1 env  in
                uu____77375 uu____77374  in
              uu____77359 uu____77268  in
            (uu____77267,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____77259  in
        [uu____77258]  in
      uu____77163 :: uu____77255  in
    uu____77099 :: uu____77160  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____77422 =
      let uu____77423 =
        let uu____77431 =
          let uu____77432 = FStar_TypeChecker_Env.get_range env  in
          let uu____77433 =
            let uu____77444 =
              let uu____77449 =
                let uu____77452 = FStar_SMTEncoding_Term.boxString b  in
                [uu____77452]  in
              [uu____77449]  in
            let uu____77457 =
              let uu____77458 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____77458 tt  in
            (uu____77444, [bb], uu____77457)  in
          FStar_SMTEncoding_Term.mkForall uu____77432 uu____77433  in
        (uu____77431, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77423  in
    let uu____77483 =
      let uu____77486 =
        let uu____77487 =
          let uu____77495 =
            let uu____77496 =
              let uu____77507 =
                let uu____77508 =
                  let uu____77513 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____77513)  in
                FStar_SMTEncoding_Util.mkImp uu____77508  in
              ([[typing_pred]], [xx], uu____77507)  in
            let uu____77540 =
              let uu____77555 = FStar_TypeChecker_Env.get_range env  in
              let uu____77556 = mkForall_fuel1 env  in
              uu____77556 uu____77555  in
            uu____77540 uu____77496  in
          (uu____77495, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____77487  in
      [uu____77486]  in
    uu____77422 :: uu____77483  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____77603 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____77603]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____77633 =
      let uu____77634 =
        let uu____77642 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____77642, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77634  in
    [uu____77633]  in
  let mk_and_interp env conj uu____77665 =
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
    let uu____77694 =
      let uu____77695 =
        let uu____77703 =
          let uu____77704 = FStar_TypeChecker_Env.get_range env  in
          let uu____77705 =
            let uu____77716 =
              let uu____77717 =
                let uu____77722 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____77722, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77717  in
            ([[l_and_a_b]], [aa; bb], uu____77716)  in
          FStar_SMTEncoding_Term.mkForall uu____77704 uu____77705  in
        (uu____77703, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77695  in
    [uu____77694]  in
  let mk_or_interp env disj uu____77777 =
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
    let uu____77806 =
      let uu____77807 =
        let uu____77815 =
          let uu____77816 = FStar_TypeChecker_Env.get_range env  in
          let uu____77817 =
            let uu____77828 =
              let uu____77829 =
                let uu____77834 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____77834, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77829  in
            ([[l_or_a_b]], [aa; bb], uu____77828)  in
          FStar_SMTEncoding_Term.mkForall uu____77816 uu____77817  in
        (uu____77815, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77807  in
    [uu____77806]  in
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
    let uu____77912 =
      let uu____77913 =
        let uu____77921 =
          let uu____77922 = FStar_TypeChecker_Env.get_range env  in
          let uu____77923 =
            let uu____77934 =
              let uu____77935 =
                let uu____77940 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____77940, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____77935  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____77934)  in
          FStar_SMTEncoding_Term.mkForall uu____77922 uu____77923  in
        (uu____77921, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____77913  in
    [uu____77912]  in
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
    let uu____78030 =
      let uu____78031 =
        let uu____78039 =
          let uu____78040 = FStar_TypeChecker_Env.get_range env  in
          let uu____78041 =
            let uu____78052 =
              let uu____78053 =
                let uu____78058 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____78058, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78053  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____78052)  in
          FStar_SMTEncoding_Term.mkForall uu____78040 uu____78041  in
        (uu____78039, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78031  in
    [uu____78030]  in
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
    let uu____78158 =
      let uu____78159 =
        let uu____78167 =
          let uu____78168 = FStar_TypeChecker_Env.get_range env  in
          let uu____78169 =
            let uu____78180 =
              let uu____78181 =
                let uu____78186 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____78186, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78181  in
            ([[l_imp_a_b]], [aa; bb], uu____78180)  in
          FStar_SMTEncoding_Term.mkForall uu____78168 uu____78169  in
        (uu____78167, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78159  in
    [uu____78158]  in
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
    let uu____78270 =
      let uu____78271 =
        let uu____78279 =
          let uu____78280 = FStar_TypeChecker_Env.get_range env  in
          let uu____78281 =
            let uu____78292 =
              let uu____78293 =
                let uu____78298 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____78298, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____78293  in
            ([[l_iff_a_b]], [aa; bb], uu____78292)  in
          FStar_SMTEncoding_Term.mkForall uu____78280 uu____78281  in
        (uu____78279, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78271  in
    [uu____78270]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____78369 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____78369  in
    let uu____78374 =
      let uu____78375 =
        let uu____78383 =
          let uu____78384 = FStar_TypeChecker_Env.get_range env  in
          let uu____78385 =
            let uu____78396 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____78396)  in
          FStar_SMTEncoding_Term.mkForall uu____78384 uu____78385  in
        (uu____78383, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78375  in
    [uu____78374]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____78449 =
      let uu____78450 =
        let uu____78458 =
          let uu____78459 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____78459 range_ty  in
        let uu____78460 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____78458, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____78460)
         in
      FStar_SMTEncoding_Util.mkAssume uu____78450  in
    [uu____78449]  in
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
        let uu____78506 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____78506 x1 t  in
      let uu____78508 = FStar_TypeChecker_Env.get_range env  in
      let uu____78509 =
        let uu____78520 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____78520)  in
      FStar_SMTEncoding_Term.mkForall uu____78508 uu____78509  in
    let uu____78545 =
      let uu____78546 =
        let uu____78554 =
          let uu____78555 = FStar_TypeChecker_Env.get_range env  in
          let uu____78556 =
            let uu____78567 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____78567)  in
          FStar_SMTEncoding_Term.mkForall uu____78555 uu____78556  in
        (uu____78554,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78546  in
    [uu____78545]  in
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
    let uu____78628 =
      let uu____78629 =
        let uu____78637 =
          let uu____78638 = FStar_TypeChecker_Env.get_range env  in
          let uu____78639 =
            let uu____78655 =
              let uu____78656 =
                let uu____78661 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____78662 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____78661, uu____78662)  in
              FStar_SMTEncoding_Util.mkAnd uu____78656  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____78655)
             in
          FStar_SMTEncoding_Term.mkForall' uu____78638 uu____78639  in
        (uu____78637,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____78629  in
    [uu____78628]  in
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
          let uu____79220 =
            FStar_Util.find_opt
              (fun uu____79258  ->
                 match uu____79258 with
                 | (l,uu____79274) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____79220 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____79317,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____79378 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____79378 with
        | (form,decls) ->
            let uu____79387 =
              let uu____79390 =
                let uu____79393 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____79393]  in
              FStar_All.pipe_right uu____79390
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____79387
  
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
              let uu____79452 =
                ((let uu____79456 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____79456) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____79452
              then
                let arg_sorts =
                  let uu____79468 =
                    let uu____79469 = FStar_Syntax_Subst.compress t_norm  in
                    uu____79469.FStar_Syntax_Syntax.n  in
                  match uu____79468 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79475) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____79513  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____79520 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____79522 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____79522 with
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
                    let uu____79558 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____79558, env1)
              else
                (let uu____79563 = prims.is lid  in
                 if uu____79563
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____79572 = prims.mk lid vname  in
                   match uu____79572 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____79596 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____79596, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____79605 =
                      let uu____79624 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____79624 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____79652 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____79652
                            then
                              let uu____79657 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___931_79660 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___931_79660.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___931_79660.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___931_79660.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___931_79660.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___931_79660.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___931_79660.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___931_79660.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___931_79660.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___931_79660.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___931_79660.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___931_79660.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___931_79660.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___931_79660.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___931_79660.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___931_79660.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___931_79660.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___931_79660.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___931_79660.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___931_79660.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___931_79660.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___931_79660.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___931_79660.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___931_79660.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___931_79660.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___931_79660.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___931_79660.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___931_79660.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___931_79660.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___931_79660.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___931_79660.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___931_79660.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___931_79660.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___931_79660.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___931_79660.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___931_79660.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___931_79660.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___931_79660.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___931_79660.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___931_79660.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___931_79660.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___931_79660.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___931_79660.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____79657
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____79683 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____79683)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____79605 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___639_79789  ->
                                  match uu___639_79789 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____79793 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79793 with
                                       | (uu____79826,xxv) ->
                                           let xx =
                                             let uu____79865 =
                                               let uu____79866 =
                                                 let uu____79872 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79872,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79866
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79865
                                              in
                                           let uu____79875 =
                                             let uu____79876 =
                                               let uu____79884 =
                                                 let uu____79885 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____79886 =
                                                   let uu____79897 =
                                                     let uu____79898 =
                                                       let uu____79903 =
                                                         let uu____79904 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____79904
                                                          in
                                                       (vapp, uu____79903)
                                                        in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____79898
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____79897)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____79885 uu____79886
                                                  in
                                               (uu____79884,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____79876
                                              in
                                           [uu____79875])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____79919 =
                                        FStar_Util.prefix vars  in
                                      (match uu____79919 with
                                       | (uu____79952,xxv) ->
                                           let xx =
                                             let uu____79991 =
                                               let uu____79992 =
                                                 let uu____79998 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____79998,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____79992
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____79991
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
                                           let uu____80009 =
                                             let uu____80010 =
                                               let uu____80018 =
                                                 let uu____80019 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____80020 =
                                                   let uu____80031 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____80031)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____80019 uu____80020
                                                  in
                                               (uu____80018,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____80010
                                              in
                                           [uu____80009])
                                  | uu____80044 -> []))
                           in
                        let uu____80045 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____80045 with
                         | (vars,guards,env',decls1,uu____80070) ->
                             let uu____80083 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____80096 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____80096, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____80100 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____80100 with
                                    | (g,ds) ->
                                        let uu____80113 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____80113,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____80083 with
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
                                  let should_thunk uu____80136 =
                                    let is_type1 t =
                                      let uu____80144 =
                                        let uu____80145 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____80145.FStar_Syntax_Syntax.n  in
                                      match uu____80144 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____80149 -> true
                                      | uu____80151 -> false  in
                                    let is_squash1 t =
                                      let uu____80160 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____80160 with
                                      | (head1,uu____80179) ->
                                          let uu____80204 =
                                            let uu____80205 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____80205.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____80204 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____80210;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____80211;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____80213;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____80214;_};_},uu____80215)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____80223 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____80228 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____80228))
                                       &&
                                       (let uu____80234 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____80234))
                                      &&
                                      (let uu____80237 = is_type1 t_norm  in
                                       Prims.op_Negation uu____80237)
                                     in
                                  let uu____80239 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____80298 -> (false, vars)  in
                                  (match uu____80239 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____80348 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____80348 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____80384 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____80393 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____80393
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____80404 ->
                                                  let uu____80413 =
                                                    let uu____80421 =
                                                      get_vtok ()  in
                                                    (uu____80421, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____80413
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____80428 =
                                                let uu____80436 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____80436)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____80428
                                               in
                                            let uu____80450 =
                                              let vname_decl =
                                                let uu____80458 =
                                                  let uu____80470 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____80470,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____80458
                                                 in
                                              let uu____80481 =
                                                let env2 =
                                                  let uu___1026_80487 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___1026_80487.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____80488 =
                                                  let uu____80490 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____80490
                                                   in
                                                if uu____80488
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____80481 with
                                              | (tok_typing,decls2) ->
                                                  let uu____80507 =
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
                                                        let uu____80533 =
                                                          let uu____80536 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80536
                                                           in
                                                        let uu____80543 =
                                                          let uu____80544 =
                                                            let uu____80547 =
                                                              let uu____80548
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____80548
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _80552  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _80552)
                                                              uu____80547
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____80544
                                                           in
                                                        (uu____80533,
                                                          uu____80543)
                                                    | uu____80559 when
                                                        thunked ->
                                                        let uu____80570 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____80570
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____80585
                                                                 =
                                                                 let uu____80593
                                                                   =
                                                                   let uu____80596
                                                                    =
                                                                    let uu____80599
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____80599]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____80596
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____80593)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____80585
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____80607
                                                               =
                                                               let uu____80615
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____80615,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.op_Hat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____80607
                                                              in
                                                           let uu____80620 =
                                                             let uu____80623
                                                               =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____80623
                                                              in
                                                           (uu____80620,
                                                             env1))
                                                    | uu____80632 ->
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
                                                          let uu____80656 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____80657 =
                                                            let uu____80668 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____80668)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____80656
                                                            uu____80657
                                                           in
                                                        let name_tok_corr =
                                                          let uu____80678 =
                                                            let uu____80686 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____80686,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____80678
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
                                                            let uu____80697 =
                                                              let uu____80698
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____80698]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____80697
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____80725 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80726 =
                                                              let uu____80737
                                                                =
                                                                let uu____80738
                                                                  =
                                                                  let uu____80743
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____80744
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____80743,
                                                                    uu____80744)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____80738
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____80737)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80725
                                                              uu____80726
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____80773 =
                                                          let uu____80776 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80776
                                                           in
                                                        (uu____80773, env1)
                                                     in
                                                  (match uu____80507 with
                                                   | (tok_decl,env2) ->
                                                       let uu____80797 =
                                                         let uu____80800 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____80800
                                                           tok_decl
                                                          in
                                                       (uu____80797, env2))
                                               in
                                            (match uu____80450 with
                                             | (decls2,env2) ->
                                                 let uu____80819 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____80829 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____80829 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____80844 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____80844, decls)
                                                    in
                                                 (match uu____80819 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____80859 =
                                                          let uu____80867 =
                                                            let uu____80868 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80869 =
                                                              let uu____80880
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____80880)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____80868
                                                              uu____80869
                                                             in
                                                          (uu____80867,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____80859
                                                         in
                                                      let freshness =
                                                        let uu____80896 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____80896
                                                        then
                                                          let uu____80904 =
                                                            let uu____80905 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____80906 =
                                                              let uu____80919
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____80926
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____80919,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____80926)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____80905
                                                              uu____80906
                                                             in
                                                          let uu____80932 =
                                                            let uu____80935 =
                                                              let uu____80936
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____80936
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____80935]  in
                                                          uu____80904 ::
                                                            uu____80932
                                                        else []  in
                                                      let g =
                                                        let uu____80942 =
                                                          let uu____80945 =
                                                            let uu____80948 =
                                                              let uu____80951
                                                                =
                                                                let uu____80954
                                                                  =
                                                                  let uu____80957
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____80957
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____80954
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____80951
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____80948
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____80945
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____80942
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
          let uu____80997 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____80997 with
          | FStar_Pervasives_Native.None  ->
              let uu____81008 = encode_free_var false env x t t_norm []  in
              (match uu____81008 with
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
            let uu____81071 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____81071 with
            | (decls,env1) ->
                let uu____81082 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____81082
                then
                  let uu____81089 =
                    let uu____81090 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____81090  in
                  (uu____81089, env1)
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
             (fun uu____81146  ->
                fun lb  ->
                  match uu____81146 with
                  | (decls,env1) ->
                      let uu____81166 =
                        let uu____81171 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____81171
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____81166 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____81200 = FStar_Syntax_Util.head_and_args t  in
    match uu____81200 with
    | (hd1,args) ->
        let uu____81244 =
          let uu____81245 = FStar_Syntax_Util.un_uinst hd1  in
          uu____81245.FStar_Syntax_Syntax.n  in
        (match uu____81244 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____81251,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____81275 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____81286 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___1113_81294 = en  in
    let uu____81295 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___1113_81294.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___1113_81294.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___1113_81294.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___1113_81294.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn =
        (uu___1113_81294.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___1113_81294.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___1113_81294.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___1113_81294.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___1113_81294.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___1113_81294.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____81295
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____81325  ->
      fun quals  ->
        match uu____81325 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____81430 = FStar_Util.first_N nbinders formals  in
              match uu____81430 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____81531  ->
                         fun uu____81532  ->
                           match (uu____81531, uu____81532) with
                           | ((formal,uu____81558),(binder,uu____81560)) ->
                               let uu____81581 =
                                 let uu____81588 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____81588)  in
                               FStar_Syntax_Syntax.NT uu____81581) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____81602 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____81643  ->
                              match uu____81643 with
                              | (x,i) ->
                                  let uu____81662 =
                                    let uu___1139_81663 = x  in
                                    let uu____81664 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1139_81663.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1139_81663.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____81664
                                    }  in
                                  (uu____81662, i)))
                       in
                    FStar_All.pipe_right uu____81602
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____81688 =
                      let uu____81693 = FStar_Syntax_Subst.compress body  in
                      let uu____81694 =
                        let uu____81695 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____81695
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____81693
                        uu____81694
                       in
                    uu____81688 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1146_81746 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1146_81746.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1146_81746.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1146_81746.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1146_81746.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1146_81746.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1146_81746.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1146_81746.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1146_81746.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1146_81746.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1146_81746.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___1146_81746.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1146_81746.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1146_81746.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1146_81746.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1146_81746.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1146_81746.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1146_81746.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1146_81746.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1146_81746.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1146_81746.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1146_81746.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1146_81746.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1146_81746.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1146_81746.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1146_81746.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1146_81746.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___1146_81746.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1146_81746.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___1146_81746.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1146_81746.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1146_81746.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1146_81746.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1146_81746.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1146_81746.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1146_81746.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1146_81746.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1146_81746.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___1146_81746.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1146_81746.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1146_81746.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1146_81746.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1146_81746.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____81818  ->
                       fun uu____81819  ->
                         match (uu____81818, uu____81819) with
                         | ((x,uu____81845),(b,uu____81847)) ->
                             let uu____81868 =
                               let uu____81875 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____81875)  in
                             FStar_Syntax_Syntax.NT uu____81868) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____81900 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____81900
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____81929 ->
                    let uu____81936 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____81936
                | uu____81937 when Prims.op_Negation norm1 ->
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
                | uu____81940 ->
                    let uu____81941 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____81941)
                 in
              let aux t1 e1 =
                let uu____81983 = FStar_Syntax_Util.abs_formals e1  in
                match uu____81983 with
                | (binders,body,lopt) ->
                    let uu____82015 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____82031 -> arrow_formals_comp_norm false t1  in
                    (match uu____82015 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____82065 =
                           if nformals < nbinders
                           then
                             let uu____82109 =
                               FStar_Util.first_N nformals binders  in
                             match uu____82109 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____82193 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____82193)
                           else
                             if nformals > nbinders
                             then
                               (let uu____82233 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____82233 with
                                | (binders1,body1) ->
                                    let uu____82286 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____82286))
                             else
                               (let uu____82299 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____82299))
                            in
                         (match uu____82065 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____82359 = aux t e  in
              match uu____82359 with
              | (binders,body,comp) ->
                  let uu____82405 =
                    let uu____82416 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____82416
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____82431 = aux comp1 body1  in
                      match uu____82431 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____82405 with
                   | (binders1,body1,comp1) ->
                       let uu____82514 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____82514, comp1))
               in
            (try
               (fun uu___1216_82541  ->
                  match () with
                  | () ->
                      let uu____82548 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____82548
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____82564 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____82627  ->
                                   fun lb  ->
                                     match uu____82627 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____82682 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____82682
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____82688 =
                                             let uu____82697 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____82697
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____82688 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____82564 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____82838;
                                    FStar_Syntax_Syntax.lbeff = uu____82839;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____82841;
                                    FStar_Syntax_Syntax.lbpos = uu____82842;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____82866 =
                                     let uu____82873 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____82873 with
                                     | (tcenv',uu____82889,e_t) ->
                                         let uu____82895 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____82906 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____82895 with
                                          | (e1,t_norm1) ->
                                              ((let uu___1279_82923 = env2
                                                   in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___1279_82923.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____82866 with
                                    | (env',e1,t_norm1) ->
                                        let uu____82933 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____82933 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____82953 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____82953
                                               then
                                                 let uu____82958 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____82961 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____82958 uu____82961
                                               else ());
                                              (let uu____82966 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____82966 with
                                               | (vars,_guards,env'1,binder_decls,uu____82993)
                                                   ->
                                                   let uu____83006 =
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
                                                         let uu____83023 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____83023
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____83045 =
                                                          let uu____83046 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____83047 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____83046 fvb
                                                            uu____83047
                                                           in
                                                        (vars, uu____83045))
                                                      in
                                                   (match uu____83006 with
                                                    | (vars1,app) ->
                                                        let uu____83058 =
                                                          let is_logical =
                                                            let uu____83071 =
                                                              let uu____83072
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____83072.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____83071
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____83078 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____83082 =
                                                              let uu____83083
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____83083
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____83082
                                                              (fun lid  ->
                                                                 let uu____83092
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____83092
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____83093 =
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
                                                          if uu____83093
                                                          then
                                                            let uu____83109 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____83110 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____83109,
                                                              uu____83110)
                                                          else
                                                            (let uu____83121
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____83121))
                                                           in
                                                        (match uu____83058
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____83145
                                                                 =
                                                                 let uu____83153
                                                                   =
                                                                   let uu____83154
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____83155
                                                                    =
                                                                    let uu____83166
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____83166)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____83154
                                                                    uu____83155
                                                                    in
                                                                 let uu____83175
                                                                   =
                                                                   let uu____83176
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____83176
                                                                    in
                                                                 (uu____83153,
                                                                   uu____83175,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____83145
                                                                in
                                                             let uu____83182
                                                               =
                                                               let uu____83185
                                                                 =
                                                                 let uu____83188
                                                                   =
                                                                   let uu____83191
                                                                    =
                                                                    let uu____83194
                                                                    =
                                                                    let uu____83197
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____83197
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____83194
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____83191
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____83188
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____83185
                                                                in
                                                             (uu____83182,
                                                               env2)))))))
                               | uu____83206 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____83266 =
                                   let uu____83272 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____83272,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____83266  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____83278 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____83331  ->
                                         fun fvb  ->
                                           match uu____83331 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____83386 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83386
                                                  in
                                               let gtok =
                                                 let uu____83390 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____83390
                                                  in
                                               let env4 =
                                                 let uu____83393 =
                                                   let uu____83396 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _83402  ->
                                                        FStar_Pervasives_Native.Some
                                                          _83402) uu____83396
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____83393
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____83278 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____83522
                                     t_norm uu____83524 =
                                     match (uu____83522, uu____83524) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____83554;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____83555;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____83557;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____83558;_})
                                         ->
                                         let uu____83585 =
                                           let uu____83592 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____83592 with
                                           | (tcenv',uu____83608,e_t) ->
                                               let uu____83614 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____83625 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____83614 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___1366_83642 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___1366_83642.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____83585 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____83655 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____83655
                                                then
                                                  let uu____83660 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____83662 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____83664 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____83660 uu____83662
                                                    uu____83664
                                                else ());
                                               (let uu____83669 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____83669 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____83696 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____83696 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____83718 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____83718
                                                           then
                                                             let uu____83723
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____83725
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____83728
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____83730
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____83723
                                                               uu____83725
                                                               uu____83728
                                                               uu____83730
                                                           else ());
                                                          (let uu____83735 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____83735
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____83764)
                                                               ->
                                                               let uu____83777
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____83790
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____83790,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____83794
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____83794
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____83807
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____83807,
                                                                    decls0))
                                                                  in
                                                               (match uu____83777
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
                                                                    let uu____83828
                                                                    =
                                                                    let uu____83840
                                                                    =
                                                                    let uu____83843
                                                                    =
                                                                    let uu____83846
                                                                    =
                                                                    let uu____83849
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____83849
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____83846
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____83843
                                                                     in
                                                                    (g,
                                                                    uu____83840,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____83828
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
                                                                    let uu____83879
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____83879
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
                                                                    let uu____83894
                                                                    =
                                                                    let uu____83897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____83897
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83894
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____83903
                                                                    =
                                                                    let uu____83906
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____83906
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____83903
                                                                     in
                                                                    let uu____83911
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____83911
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____83927
                                                                    =
                                                                    let uu____83935
                                                                    =
                                                                    let uu____83936
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83937
                                                                    =
                                                                    let uu____83953
                                                                    =
                                                                    let uu____83954
                                                                    =
                                                                    let uu____83959
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____83959)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____83954
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____83953)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____83936
                                                                    uu____83937
                                                                     in
                                                                    let uu____83973
                                                                    =
                                                                    let uu____83974
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____83974
                                                                     in
                                                                    (uu____83935,
                                                                    uu____83973,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83927
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____83981
                                                                    =
                                                                    let uu____83989
                                                                    =
                                                                    let uu____83990
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____83991
                                                                    =
                                                                    let uu____84002
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____84002)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____83990
                                                                    uu____83991
                                                                     in
                                                                    (uu____83989,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____83981
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____84016
                                                                    =
                                                                    let uu____84024
                                                                    =
                                                                    let uu____84025
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84026
                                                                    =
                                                                    let uu____84037
                                                                    =
                                                                    let uu____84038
                                                                    =
                                                                    let uu____84043
                                                                    =
                                                                    let uu____84044
                                                                    =
                                                                    let uu____84047
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____84047
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____84044
                                                                     in
                                                                    (gsapp,
                                                                    uu____84043)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____84038
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84037)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84025
                                                                    uu____84026
                                                                     in
                                                                    (uu____84024,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84016
                                                                     in
                                                                    let uu____84061
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
                                                                    let uu____84073
                                                                    =
                                                                    let uu____84074
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____84074
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____84073
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____84076
                                                                    =
                                                                    let uu____84084
                                                                    =
                                                                    let uu____84085
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84086
                                                                    =
                                                                    let uu____84097
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84097)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84085
                                                                    uu____84086
                                                                     in
                                                                    (uu____84084,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84076
                                                                     in
                                                                    let uu____84110
                                                                    =
                                                                    let uu____84119
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____84119
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____84134
                                                                    =
                                                                    let uu____84137
                                                                    =
                                                                    let uu____84138
                                                                    =
                                                                    let uu____84146
                                                                    =
                                                                    let uu____84147
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____84148
                                                                    =
                                                                    let uu____84159
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____84159)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____84147
                                                                    uu____84148
                                                                     in
                                                                    (uu____84146,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____84138
                                                                     in
                                                                    [uu____84137]
                                                                     in
                                                                    (d3,
                                                                    uu____84134)
                                                                     in
                                                                    match uu____84110
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____84061
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____84216
                                                                    =
                                                                    let uu____84219
                                                                    =
                                                                    let uu____84222
                                                                    =
                                                                    let uu____84225
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____84225
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____84222
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____84219
                                                                     in
                                                                    let uu____84232
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____84216,
                                                                    uu____84232,
                                                                    env02))))))))))
                                      in
                                   let uu____84237 =
                                     let uu____84250 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____84313  ->
                                          fun uu____84314  ->
                                            match (uu____84313, uu____84314)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____84439 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____84439 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____84250
                                      in
                                   (match uu____84237 with
                                    | (decls2,eqns,env01) ->
                                        let uu____84506 =
                                          let isDeclFun uu___640_84523 =
                                            match uu___640_84523 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____84525 -> true
                                            | uu____84538 -> false  in
                                          let uu____84540 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____84540
                                            (fun decls3  ->
                                               let uu____84570 =
                                                 FStar_List.fold_left
                                                   (fun uu____84601  ->
                                                      fun elt  ->
                                                        match uu____84601
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____84642 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____84642
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____84670
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____84670
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
                                                                    let uu___1459_84708
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___1459_84708.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___1459_84708.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___1459_84708.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____84570 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____84740 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____84740, elts, rest))
                                           in
                                        (match uu____84506 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____84769 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___641_84775  ->
                                        match uu___641_84775 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____84778 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____84786 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____84786)))
                                in
                             if uu____84769
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___1476_84808  ->
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
                   let uu____84847 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____84847
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____84866 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____84866, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____84922 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____84922 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____84928 = encode_sigelt' env se  in
      match uu____84928 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____84940 =
                  let uu____84943 =
                    let uu____84944 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____84944  in
                  [uu____84943]  in
                FStar_All.pipe_right uu____84940
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____84949 ->
                let uu____84950 =
                  let uu____84953 =
                    let uu____84956 =
                      let uu____84957 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____84957  in
                    [uu____84956]  in
                  FStar_All.pipe_right uu____84953
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____84964 =
                  let uu____84967 =
                    let uu____84970 =
                      let uu____84973 =
                        let uu____84974 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____84974  in
                      [uu____84973]  in
                    FStar_All.pipe_right uu____84970
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____84967  in
                FStar_List.append uu____84950 uu____84964
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____84988 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____84988
       then
         let uu____84993 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____84993
       else ());
      (let is_opaque_to_smt t =
         let uu____85005 =
           let uu____85006 = FStar_Syntax_Subst.compress t  in
           uu____85006.FStar_Syntax_Syntax.n  in
         match uu____85005 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85011)) -> s = "opaque_to_smt"
         | uu____85016 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____85025 =
           let uu____85026 = FStar_Syntax_Subst.compress t  in
           uu____85026.FStar_Syntax_Syntax.n  in
         match uu____85025 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____85031)) -> s = "uninterpreted_by_smt"
         | uu____85036 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85042 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____85048 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____85060 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____85061 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____85062 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____85075 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____85077 =
             let uu____85079 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____85079  in
           if uu____85077
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____85108 ->
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
                let uu____85140 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____85140 with
                | (formals,uu____85160) ->
                    let arity = FStar_List.length formals  in
                    let uu____85184 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____85184 with
                     | (aname,atok,env2) ->
                         let uu____85210 =
                           let uu____85215 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____85215 env2
                            in
                         (match uu____85210 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____85227 =
                                  let uu____85228 =
                                    let uu____85240 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____85260  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____85240,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____85228
                                   in
                                [uu____85227;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____85277 =
                                let aux uu____85323 uu____85324 =
                                  match (uu____85323, uu____85324) with
                                  | ((bv,uu____85368),(env3,acc_sorts,acc))
                                      ->
                                      let uu____85400 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____85400 with
                                       | (xxsym,xx,env4) ->
                                           let uu____85423 =
                                             let uu____85426 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____85426 :: acc_sorts  in
                                           (env4, uu____85423, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____85277 with
                               | (uu____85458,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____85474 =
                                       let uu____85482 =
                                         let uu____85483 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85484 =
                                           let uu____85495 =
                                             let uu____85496 =
                                               let uu____85501 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____85501)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____85496
                                              in
                                           ([[app]], xs_sorts, uu____85495)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85483 uu____85484
                                          in
                                       (uu____85482,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85474
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____85516 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____85516
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____85519 =
                                       let uu____85527 =
                                         let uu____85528 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____85529 =
                                           let uu____85540 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____85540)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____85528 uu____85529
                                          in
                                       (uu____85527,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____85519
                                      in
                                   let uu____85553 =
                                     let uu____85556 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____85556  in
                                   (env2, uu____85553))))
                 in
              let uu____85565 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____85565 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85591,uu____85592)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____85593 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____85593 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____85615,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____85622 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___642_85628  ->
                       match uu___642_85628 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____85631 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____85637 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____85640 -> false))
                in
             Prims.op_Negation uu____85622  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____85650 =
                let uu____85655 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____85655 env fv t quals  in
              match uu____85650 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____85669 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____85669  in
                  let uu____85672 =
                    let uu____85673 =
                      let uu____85676 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____85676
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____85673  in
                  (uu____85672, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____85686 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____85686 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1612_85698 = env  in
                  let uu____85699 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1612_85698.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1612_85698.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1612_85698.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____85699;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1612_85698.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1612_85698.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1612_85698.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1612_85698.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1612_85698.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1612_85698.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1612_85698.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____85701 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____85701 with
                 | (f3,decls) ->
                     let g =
                       let uu____85715 =
                         let uu____85718 =
                           let uu____85719 =
                             let uu____85727 =
                               let uu____85728 =
                                 let uu____85730 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____85730
                                  in
                               FStar_Pervasives_Native.Some uu____85728  in
                             let uu____85734 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____85727, uu____85734)  in
                           FStar_SMTEncoding_Util.mkAssume uu____85719  in
                         [uu____85718]  in
                       FStar_All.pipe_right uu____85715
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____85743) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____85757 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____85779 =
                        let uu____85782 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____85782.FStar_Syntax_Syntax.fv_name  in
                      uu____85779.FStar_Syntax_Syntax.v  in
                    let uu____85783 =
                      let uu____85785 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____85785  in
                    if uu____85783
                    then
                      let val_decl =
                        let uu___1629_85817 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1629_85817.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1629_85817.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1629_85817.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____85818 = encode_sigelt' env1 val_decl  in
                      match uu____85818 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____85757 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____85854,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____85856;
                           FStar_Syntax_Syntax.lbtyp = uu____85857;
                           FStar_Syntax_Syntax.lbeff = uu____85858;
                           FStar_Syntax_Syntax.lbdef = uu____85859;
                           FStar_Syntax_Syntax.lbattrs = uu____85860;
                           FStar_Syntax_Syntax.lbpos = uu____85861;_}::[]),uu____85862)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____85881 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____85881 with
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
                  let uu____85919 =
                    let uu____85922 =
                      let uu____85923 =
                        let uu____85931 =
                          let uu____85932 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____85933 =
                            let uu____85944 =
                              let uu____85945 =
                                let uu____85950 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____85950)  in
                              FStar_SMTEncoding_Util.mkEq uu____85945  in
                            ([[b2t_x]], [xx], uu____85944)  in
                          FStar_SMTEncoding_Term.mkForall uu____85932
                            uu____85933
                           in
                        (uu____85931,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____85923  in
                    [uu____85922]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____85919
                   in
                let uu____85988 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____85988, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____85991,uu____85992) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___643_86002  ->
                   match uu___643_86002 with
                   | FStar_Syntax_Syntax.Discriminator uu____86004 -> true
                   | uu____86006 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____86008,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____86020 =
                      let uu____86022 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____86022.FStar_Ident.idText  in
                    uu____86020 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___644_86029  ->
                      match uu___644_86029 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____86032 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____86035) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___645_86049  ->
                   match uu___645_86049 with
                   | FStar_Syntax_Syntax.Projector uu____86051 -> true
                   | uu____86057 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____86061 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____86061 with
            | FStar_Pervasives_Native.Some uu____86068 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1694_86070 = se  in
                  let uu____86071 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____86071;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1694_86070.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1694_86070.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1694_86070.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____86074) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____86089) ->
           let uu____86098 = encode_sigelts env ses  in
           (match uu____86098 with
            | (g,env1) ->
                let uu____86109 =
                  FStar_List.fold_left
                    (fun uu____86133  ->
                       fun elt  ->
                         match uu____86133 with
                         | (g',inversions) ->
                             let uu____86161 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___646_86184  ->
                                       match uu___646_86184 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____86186;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____86187;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____86188;_}
                                           -> false
                                       | uu____86195 -> true))
                                in
                             (match uu____86161 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1726_86220 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1726_86220.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1726_86220.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1726_86220.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____86109 with
                 | (g',inversions) ->
                     let uu____86239 =
                       FStar_List.fold_left
                         (fun uu____86270  ->
                            fun elt  ->
                              match uu____86270 with
                              | (decls,elts,rest) ->
                                  let uu____86311 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___647_86320  ->
                                            match uu___647_86320 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____86322 -> true
                                            | uu____86335 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____86311
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____86358 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___648_86379  ->
                                               match uu___648_86379 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____86381 -> true
                                               | uu____86394 -> false))
                                        in
                                     match uu____86358 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1748_86425 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1748_86425.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1748_86425.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1748_86425.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____86239 with
                      | (decls,elts,rest) ->
                          let uu____86451 =
                            let uu____86452 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____86459 =
                              let uu____86462 =
                                let uu____86465 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____86465  in
                              FStar_List.append elts uu____86462  in
                            FStar_List.append uu____86452 uu____86459  in
                          (uu____86451, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____86476,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____86489 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____86489 with
             | (usubst,uvs) ->
                 let uu____86509 =
                   let uu____86516 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____86517 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____86518 =
                     let uu____86519 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____86519 k  in
                   (uu____86516, uu____86517, uu____86518)  in
                 (match uu____86509 with
                  | (env1,tps1,k1) ->
                      let uu____86532 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____86532 with
                       | (tps2,k2) ->
                           let uu____86540 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____86540 with
                            | (uu____86556,k3) ->
                                let uu____86578 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____86578 with
                                 | (tps3,env_tps,uu____86590,us) ->
                                     let u_k =
                                       let uu____86593 =
                                         let uu____86594 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____86595 =
                                           let uu____86600 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____86602 =
                                             let uu____86603 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____86603
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____86600 uu____86602
                                            in
                                         uu____86595
                                           FStar_Pervasives_Native.None
                                           uu____86594
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____86593 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____86623) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____86629,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____86632) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____86640,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____86647) ->
                                           let uu____86648 =
                                             let uu____86650 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86650
                                              in
                                           failwith uu____86648
                                       | (uu____86654,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____86655 =
                                             let uu____86657 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86657
                                              in
                                           failwith uu____86655
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____86661,uu____86662) ->
                                           let uu____86671 =
                                             let uu____86673 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86673
                                              in
                                           failwith uu____86671
                                       | (uu____86677,FStar_Syntax_Syntax.U_unif
                                          uu____86678) ->
                                           let uu____86687 =
                                             let uu____86689 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____86689
                                              in
                                           failwith uu____86687
                                       | uu____86693 -> false  in
                                     let u_leq_u_k u =
                                       let uu____86706 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____86706 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86724 = u_leq_u_k u_tp  in
                                       if uu____86724
                                       then true
                                       else
                                         (let uu____86731 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____86731 with
                                          | (formals,uu____86748) ->
                                              let uu____86769 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____86769 with
                                               | (uu____86779,uu____86780,uu____86781,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____86792 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____86792
             then
               let uu____86797 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____86797
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___649_86817  ->
                       match uu___649_86817 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____86821 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____86834 = c  in
                 match uu____86834 with
                 | (name,args,uu____86839,uu____86840,uu____86841) ->
                     let uu____86852 =
                       let uu____86853 =
                         let uu____86865 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____86892  ->
                                   match uu____86892 with
                                   | (uu____86901,sort,uu____86903) -> sort))
                            in
                         (name, uu____86865,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____86853  in
                     [uu____86852]
               else
                 (let uu____86914 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____86914 c)
                in
             let inversion_axioms tapp vars =
               let uu____86932 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____86940 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____86940 FStar_Option.isNone))
                  in
               if uu____86932
               then []
               else
                 (let uu____86975 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____86975 with
                  | (xxsym,xx) ->
                      let uu____86988 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____87027  ->
                                fun l  ->
                                  match uu____87027 with
                                  | (out,decls) ->
                                      let uu____87047 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____87047 with
                                       | (uu____87058,data_t) ->
                                           let uu____87060 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____87060 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____87104 =
                                                    let uu____87105 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____87105.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87104 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____87108,indices)
                                                      -> indices
                                                  | uu____87134 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____87164  ->
                                                            match uu____87164
                                                            with
                                                            | (x,uu____87172)
                                                                ->
                                                                let uu____87177
                                                                  =
                                                                  let uu____87178
                                                                    =
                                                                    let uu____87186
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____87186,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____87178
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____87177)
                                                       env)
                                                   in
                                                let uu____87191 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____87191 with
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
                                                                  let uu____87226
                                                                    =
                                                                    let uu____87231
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____87231,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____87226)
                                                             vars indices1
                                                         else []  in
                                                       let uu____87234 =
                                                         let uu____87235 =
                                                           let uu____87240 =
                                                             let uu____87241
                                                               =
                                                               let uu____87246
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____87247
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____87246,
                                                                 uu____87247)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____87241
                                                              in
                                                           (out, uu____87240)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____87235
                                                          in
                                                       (uu____87234,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____86988 with
                       | (data_ax,decls) ->
                           let uu____87262 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____87262 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____87279 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____87279 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____87286 =
                                    let uu____87294 =
                                      let uu____87295 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____87296 =
                                        let uu____87307 =
                                          let uu____87308 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____87310 =
                                            let uu____87313 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____87313 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____87308 uu____87310
                                           in
                                        let uu____87315 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____87307,
                                          uu____87315)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____87295 uu____87296
                                       in
                                    let uu____87324 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____87294,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____87324)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____87286
                                   in
                                let uu____87330 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____87330)))
                in
             let uu____87337 =
               let uu____87342 =
                 let uu____87343 = FStar_Syntax_Subst.compress k  in
                 uu____87343.FStar_Syntax_Syntax.n  in
               match uu____87342 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____87378 -> (tps, k)  in
             match uu____87337 with
             | (formals,res) ->
                 let uu____87385 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____87385 with
                  | (formals1,res1) ->
                      let uu____87396 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____87396 with
                       | (vars,guards,env',binder_decls,uu____87421) ->
                           let arity = FStar_List.length vars  in
                           let uu____87435 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____87435 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____87465 =
                                    let uu____87473 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____87473)  in
                                  FStar_SMTEncoding_Util.mkApp uu____87465
                                   in
                                let uu____87479 =
                                  let tname_decl =
                                    let uu____87489 =
                                      let uu____87490 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____87509 =
                                                  let uu____87511 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.op_Hat tname
                                                    uu____87511
                                                   in
                                                let uu____87513 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____87509, uu____87513,
                                                  false)))
                                         in
                                      let uu____87517 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____87490,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____87517, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____87489
                                     in
                                  let uu____87525 =
                                    match vars with
                                    | [] ->
                                        let uu____87538 =
                                          let uu____87539 =
                                            let uu____87542 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _87548  ->
                                                 FStar_Pervasives_Native.Some
                                                   _87548) uu____87542
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____87539
                                           in
                                        ([], uu____87538)
                                    | uu____87555 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____87565 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____87565
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____87581 =
                                            let uu____87589 =
                                              let uu____87590 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____87591 =
                                                let uu____87607 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____87607)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____87590 uu____87591
                                               in
                                            (uu____87589,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.op_Hat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____87581
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____87525 with
                                  | (tok_decls,env2) ->
                                      let uu____87634 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____87634
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____87479 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____87662 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____87662 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____87684 =
                                                 let uu____87685 =
                                                   let uu____87693 =
                                                     let uu____87694 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____87694
                                                      in
                                                   (uu____87693,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.op_Hat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____87685
                                                  in
                                               [uu____87684]
                                             else []  in
                                           let uu____87702 =
                                             let uu____87705 =
                                               let uu____87708 =
                                                 let uu____87711 =
                                                   let uu____87712 =
                                                     let uu____87720 =
                                                       let uu____87721 =
                                                         FStar_Ident.range_of_lid
                                                           t
                                                          in
                                                       let uu____87722 =
                                                         let uu____87733 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, k1)
                                                            in
                                                         ([[tapp]], vars,
                                                           uu____87733)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____87721
                                                         uu____87722
                                                        in
                                                     (uu____87720,
                                                       FStar_Pervasives_Native.None,
                                                       (Prims.op_Hat
                                                          "kinding_" ttok))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____87712
                                                    in
                                                 [uu____87711]  in
                                               FStar_List.append karr
                                                 uu____87708
                                                in
                                             FStar_All.pipe_right uu____87705
                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                              in
                                           FStar_List.append decls1
                                             uu____87702
                                        in
                                     let aux =
                                       let uu____87752 =
                                         let uu____87755 =
                                           inversion_axioms tapp vars  in
                                         let uu____87758 =
                                           let uu____87761 =
                                             let uu____87764 =
                                               let uu____87765 =
                                                 FStar_Ident.range_of_lid t
                                                  in
                                               pretype_axiom uu____87765 env2
                                                 tapp vars
                                                in
                                             [uu____87764]  in
                                           FStar_All.pipe_right uu____87761
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append uu____87755
                                           uu____87758
                                          in
                                       FStar_List.append kindingAx
                                         uu____87752
                                        in
                                     let g =
                                       let uu____87773 =
                                         FStar_All.pipe_right decls
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____87773
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87781,uu____87782,uu____87783,uu____87784,uu____87785)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____87793,t,uu____87795,n_tps,uu____87797) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____87807 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____87807 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____87855 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____87855 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____87883 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____87883 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____87903 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____87903 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____87982 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____87982,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____87989 =
                                   let uu____87990 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____87990, true)
                                    in
                                 let uu____87998 =
                                   let uu____88005 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____88005
                                    in
                                 FStar_All.pipe_right uu____87989 uu____87998
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
                               let uu____88017 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____88017 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____88029::uu____88030 ->
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
                                            let uu____88079 =
                                              let uu____88080 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____88080]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____88079
                                             in
                                          let uu____88106 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____88107 =
                                            let uu____88118 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____88118)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____88106 uu____88107
                                      | uu____88145 -> tok_typing  in
                                    let uu____88156 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____88156 with
                                     | (vars',guards',env'',decls_formals,uu____88181)
                                         ->
                                         let uu____88194 =
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
                                         (match uu____88194 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____88224 ->
                                                    let uu____88233 =
                                                      let uu____88234 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____88234
                                                       in
                                                    [uu____88233]
                                                 in
                                              let encode_elim uu____88250 =
                                                let uu____88251 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____88251 with
                                                | (head1,args) ->
                                                    let uu____88302 =
                                                      let uu____88303 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____88303.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____88302 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____88315;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____88316;_},uu____88317)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____88323 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88323
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
                                                                  | uu____88386
                                                                    ->
                                                                    let uu____88387
                                                                    =
                                                                    let uu____88393
                                                                    =
                                                                    let uu____88395
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____88395
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____88393)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____88387
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____88418
                                                                    =
                                                                    let uu____88420
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____88420
                                                                     in
                                                                    if
                                                                    uu____88418
                                                                    then
                                                                    let uu____88442
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____88442]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____88445
                                                                =
                                                                let uu____88459
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____88516
                                                                     ->
                                                                    fun
                                                                    uu____88517
                                                                     ->
                                                                    match 
                                                                    (uu____88516,
                                                                    uu____88517)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____88628
                                                                    =
                                                                    let uu____88636
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____88636
                                                                     in
                                                                    (match uu____88628
                                                                    with
                                                                    | 
                                                                    (uu____88650,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____88661
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____88661
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____88666
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____88666
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
                                                                  uu____88459
                                                                 in
                                                              (match uu____88445
                                                               with
                                                               | (uu____88687,arg_vars,elim_eqns_or_guards,uu____88690)
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
                                                                    let uu____88717
                                                                    =
                                                                    let uu____88725
                                                                    =
                                                                    let uu____88726
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88727
                                                                    =
                                                                    let uu____88738
                                                                    =
                                                                    let uu____88739
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88739
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88741
                                                                    =
                                                                    let uu____88742
                                                                    =
                                                                    let uu____88747
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____88747)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88742
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88738,
                                                                    uu____88741)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88726
                                                                    uu____88727
                                                                     in
                                                                    (uu____88725,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88717
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____88762
                                                                    =
                                                                    let uu____88763
                                                                    =
                                                                    let uu____88769
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____88769,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88763
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____88762
                                                                     in
                                                                    let uu____88772
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____88772
                                                                    then
                                                                    let x =
                                                                    let uu____88776
                                                                    =
                                                                    let uu____88782
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____88782,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____88776
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____88787
                                                                    =
                                                                    let uu____88795
                                                                    =
                                                                    let uu____88796
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88797
                                                                    =
                                                                    let uu____88808
                                                                    =
                                                                    let uu____88813
                                                                    =
                                                                    let uu____88816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____88816]
                                                                     in
                                                                    [uu____88813]
                                                                     in
                                                                    let uu____88821
                                                                    =
                                                                    let uu____88822
                                                                    =
                                                                    let uu____88827
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____88829
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____88827,
                                                                    uu____88829)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88822
                                                                     in
                                                                    (uu____88808,
                                                                    [x],
                                                                    uu____88821)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88796
                                                                    uu____88797
                                                                     in
                                                                    let uu____88850
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____88795,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____88850)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88787
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____88861
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
                                                                    (let uu____88884
                                                                    =
                                                                    let uu____88885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____88885
                                                                    dapp1  in
                                                                    [uu____88884])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____88861
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____88892
                                                                    =
                                                                    let uu____88900
                                                                    =
                                                                    let uu____88901
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____88902
                                                                    =
                                                                    let uu____88913
                                                                    =
                                                                    let uu____88914
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____88914
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____88916
                                                                    =
                                                                    let uu____88917
                                                                    =
                                                                    let uu____88922
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____88922)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____88917
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____88913,
                                                                    uu____88916)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____88901
                                                                    uu____88902
                                                                     in
                                                                    (uu____88900,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____88892)
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
                                                         let uu____88941 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____88941
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
                                                                  | uu____89004
                                                                    ->
                                                                    let uu____89005
                                                                    =
                                                                    let uu____89011
                                                                    =
                                                                    let uu____89013
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____89013
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____89011)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____89005
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____89036
                                                                    =
                                                                    let uu____89038
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____89038
                                                                     in
                                                                    if
                                                                    uu____89036
                                                                    then
                                                                    let uu____89060
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____89060]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____89063
                                                                =
                                                                let uu____89077
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____89134
                                                                     ->
                                                                    fun
                                                                    uu____89135
                                                                     ->
                                                                    match 
                                                                    (uu____89134,
                                                                    uu____89135)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____89246
                                                                    =
                                                                    let uu____89254
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____89254
                                                                     in
                                                                    (match uu____89246
                                                                    with
                                                                    | 
                                                                    (uu____89268,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____89279
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____89279
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____89284
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____89284
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
                                                                  uu____89077
                                                                 in
                                                              (match uu____89063
                                                               with
                                                               | (uu____89305,arg_vars,elim_eqns_or_guards,uu____89308)
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
                                                                    let uu____89335
                                                                    =
                                                                    let uu____89343
                                                                    =
                                                                    let uu____89344
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89345
                                                                    =
                                                                    let uu____89356
                                                                    =
                                                                    let uu____89357
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89357
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89359
                                                                    =
                                                                    let uu____89360
                                                                    =
                                                                    let uu____89365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____89365)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89360
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89356,
                                                                    uu____89359)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89344
                                                                    uu____89345
                                                                     in
                                                                    (uu____89343,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89335
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____89380
                                                                    =
                                                                    let uu____89381
                                                                    =
                                                                    let uu____89387
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____89387,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89381
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____89380
                                                                     in
                                                                    let uu____89390
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____89390
                                                                    then
                                                                    let x =
                                                                    let uu____89394
                                                                    =
                                                                    let uu____89400
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____89400,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____89394
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____89405
                                                                    =
                                                                    let uu____89413
                                                                    =
                                                                    let uu____89414
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89415
                                                                    =
                                                                    let uu____89426
                                                                    =
                                                                    let uu____89431
                                                                    =
                                                                    let uu____89434
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____89434]
                                                                     in
                                                                    [uu____89431]
                                                                     in
                                                                    let uu____89439
                                                                    =
                                                                    let uu____89440
                                                                    =
                                                                    let uu____89445
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____89447
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____89445,
                                                                    uu____89447)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89440
                                                                     in
                                                                    (uu____89426,
                                                                    [x],
                                                                    uu____89439)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89414
                                                                    uu____89415
                                                                     in
                                                                    let uu____89468
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____89413,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____89468)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89405
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____89479
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
                                                                    (let uu____89502
                                                                    =
                                                                    let uu____89503
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____89503
                                                                    dapp1  in
                                                                    [uu____89502])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____89479
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____89510
                                                                    =
                                                                    let uu____89518
                                                                    =
                                                                    let uu____89519
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89520
                                                                    =
                                                                    let uu____89531
                                                                    =
                                                                    let uu____89532
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89532
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____89534
                                                                    =
                                                                    let uu____89535
                                                                    =
                                                                    let uu____89540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____89540)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____89535
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____89531,
                                                                    uu____89534)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89519
                                                                    uu____89520
                                                                     in
                                                                    (uu____89518,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89510)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____89557 ->
                                                         ((let uu____89559 =
                                                             let uu____89565
                                                               =
                                                               let uu____89567
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____89569
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____89567
                                                                 uu____89569
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____89565)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____89559);
                                                          ([], [])))
                                                 in
                                              let uu____89577 =
                                                encode_elim ()  in
                                              (match uu____89577 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____89603 =
                                                       let uu____89606 =
                                                         let uu____89609 =
                                                           let uu____89612 =
                                                             let uu____89615
                                                               =
                                                               let uu____89618
                                                                 =
                                                                 let uu____89621
                                                                   =
                                                                   let uu____89622
                                                                    =
                                                                    let uu____89634
                                                                    =
                                                                    let uu____89635
                                                                    =
                                                                    let uu____89637
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____89637
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____89635
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____89634)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____89622
                                                                    in
                                                                 [uu____89621]
                                                                  in
                                                               FStar_List.append
                                                                 uu____89618
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____89615
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____89648 =
                                                             let uu____89651
                                                               =
                                                               let uu____89654
                                                                 =
                                                                 let uu____89657
                                                                   =
                                                                   let uu____89660
                                                                    =
                                                                    let uu____89663
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____89668
                                                                    =
                                                                    let uu____89671
                                                                    =
                                                                    let uu____89672
                                                                    =
                                                                    let uu____89680
                                                                    =
                                                                    let uu____89681
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89682
                                                                    =
                                                                    let uu____89693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____89693)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89681
                                                                    uu____89682
                                                                     in
                                                                    (uu____89680,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89672
                                                                     in
                                                                    let uu____89706
                                                                    =
                                                                    let uu____89709
                                                                    =
                                                                    let uu____89710
                                                                    =
                                                                    let uu____89718
                                                                    =
                                                                    let uu____89719
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____89720
                                                                    =
                                                                    let uu____89731
                                                                    =
                                                                    let uu____89732
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____89732
                                                                    vars'  in
                                                                    let uu____89734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____89731,
                                                                    uu____89734)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____89719
                                                                    uu____89720
                                                                     in
                                                                    (uu____89718,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____89710
                                                                     in
                                                                    [uu____89709]
                                                                     in
                                                                    uu____89671
                                                                    ::
                                                                    uu____89706
                                                                     in
                                                                    uu____89663
                                                                    ::
                                                                    uu____89668
                                                                     in
                                                                   FStar_List.append
                                                                    uu____89660
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____89657
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____89654
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____89651
                                                              in
                                                           FStar_List.append
                                                             uu____89612
                                                             uu____89648
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____89609
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____89606
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____89603
                                                      in
                                                   let uu____89751 =
                                                     let uu____89752 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____89752 g
                                                      in
                                                   (uu____89751, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____89786  ->
              fun se  ->
                match uu____89786 with
                | (g,env1) ->
                    let uu____89806 = encode_sigelt env1 se  in
                    (match uu____89806 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____89874 =
        match uu____89874 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____89911 ->
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
                 ((let uu____89919 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____89919
                   then
                     let uu____89924 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____89926 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____89928 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____89924 uu____89926 uu____89928
                   else ());
                  (let uu____89933 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____89933 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____89951 =
                         let uu____89959 =
                           let uu____89961 =
                             let uu____89963 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____89963
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____89961  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____89959
                          in
                       (match uu____89951 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____89983 = FStar_Options.log_queries ()
                                 in
                              if uu____89983
                              then
                                let uu____89986 =
                                  let uu____89988 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____89990 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____89992 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____89988 uu____89990 uu____89992
                                   in
                                FStar_Pervasives_Native.Some uu____89986
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____90008 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____90018 =
                                let uu____90021 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____90021  in
                              FStar_List.append uu____90008 uu____90018  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____90033,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____90053 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____90053 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____90074 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____90074 with | (uu____90101,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____90154  ->
              match uu____90154 with
              | (l,uu____90163,uu____90164) ->
                  let uu____90167 =
                    let uu____90179 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____90179, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____90167))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____90212  ->
              match uu____90212 with
              | (l,uu____90223,uu____90224) ->
                  let uu____90227 =
                    let uu____90228 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _90231  -> FStar_SMTEncoding_Term.Echo _90231)
                      uu____90228
                     in
                  let uu____90232 =
                    let uu____90235 =
                      let uu____90236 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____90236  in
                    [uu____90235]  in
                  uu____90227 :: uu____90232))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____90265 =
      let uu____90268 =
        let uu____90269 = FStar_Util.psmap_empty ()  in
        let uu____90284 =
          let uu____90293 = FStar_Util.psmap_empty ()  in (uu____90293, [])
           in
        let uu____90300 =
          let uu____90302 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____90302 FStar_Ident.string_of_lid  in
        let uu____90304 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____90269;
          FStar_SMTEncoding_Env.fvar_bindings = uu____90284;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____90300;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____90304
        }  in
      [uu____90268]  in
    FStar_ST.op_Colon_Equals last_env uu____90265
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____90348 = FStar_ST.op_Bang last_env  in
      match uu____90348 with
      | [] -> failwith "No env; call init first!"
      | e::uu____90376 ->
          let uu___2175_90379 = e  in
          let uu____90380 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2175_90379.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2175_90379.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2175_90379.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___2175_90379.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2175_90379.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2175_90379.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2175_90379.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____90380;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2175_90379.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2175_90379.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____90388 = FStar_ST.op_Bang last_env  in
    match uu____90388 with
    | [] -> failwith "Empty env stack"
    | uu____90415::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____90447  ->
    let uu____90448 = FStar_ST.op_Bang last_env  in
    match uu____90448 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____90508  ->
    let uu____90509 = FStar_ST.op_Bang last_env  in
    match uu____90509 with
    | [] -> failwith "Popping an empty stack"
    | uu____90536::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____90573  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____90626  ->
         let uu____90627 = snapshot_env ()  in
         match uu____90627 with
         | (env_depth,()) ->
             let uu____90649 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____90649 with
              | (varops_depth,()) ->
                  let uu____90671 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____90671 with
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
        (fun uu____90729  ->
           let uu____90730 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____90730 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____90825 = snapshot msg  in () 
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
        | (uu____90871::uu____90872,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2236_90880 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2236_90880.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2236_90880.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2236_90880.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____90881 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___2242_90908 = elt  in
        let uu____90909 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___2242_90908.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___2242_90908.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____90909;
          FStar_SMTEncoding_Term.a_names =
            (uu___2242_90908.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____90929 =
        let uu____90932 =
          let uu____90933 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____90933  in
        let uu____90934 = open_fact_db_tags env  in uu____90932 ::
          uu____90934
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____90929
  
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
      let uu____90961 = encode_sigelt env se  in
      match uu____90961 with
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
                (let uu____91007 =
                   let uu____91010 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____91010
                    in
                 match uu____91007 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____91025 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____91025
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____91055 = FStar_Options.log_queries ()  in
        if uu____91055
        then
          let uu____91060 =
            let uu____91061 =
              let uu____91063 =
                let uu____91065 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____91065 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____91063  in
            FStar_SMTEncoding_Term.Caption uu____91061  in
          uu____91060 :: decls
        else decls  in
      (let uu____91084 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____91084
       then
         let uu____91087 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____91087
       else ());
      (let env =
         let uu____91093 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____91093 tcenv  in
       let uu____91094 = encode_top_level_facts env se  in
       match uu____91094 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____91108 =
               let uu____91111 =
                 let uu____91114 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____91114
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____91111  in
             FStar_SMTEncoding_Z3.giveZ3 uu____91108)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____91147 = FStar_Options.log_queries ()  in
          if uu____91147
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___2280_91167 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___2280_91167.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___2280_91167.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___2280_91167.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___2280_91167.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___2280_91167.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___2280_91167.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___2280_91167.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___2280_91167.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___2280_91167.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___2280_91167.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____91172 =
             let uu____91175 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____91175
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____91172  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____91195 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____91195
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
          (let uu____91219 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____91219
           then
             let uu____91222 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____91222
           else ());
          (let env =
             let uu____91230 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____91230
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____91269  ->
                     fun se  ->
                       match uu____91269 with
                       | (g,env2) ->
                           let uu____91289 = encode_top_level_facts env2 se
                              in
                           (match uu____91289 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____91312 =
             encode_signature
               (let uu___2303_91321 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___2303_91321.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___2303_91321.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___2303_91321.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___2303_91321.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___2303_91321.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___2303_91321.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___2303_91321.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___2303_91321.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___2303_91321.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___2303_91321.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____91312 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____91337 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91337
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____91343 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____91343))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____91371  ->
        match uu____91371 with
        | (decls,fvbs) ->
            ((let uu____91385 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____91385
              then ()
              else
                (let uu____91390 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____91390
                 then
                   let uu____91393 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____91393
                 else ()));
             (let env =
                let uu____91401 = get_env name tcenv  in
                FStar_All.pipe_right uu____91401
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____91403 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____91403
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____91417 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____91417
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
        (let uu____91479 =
           let uu____91481 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____91481.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____91479);
        (let env =
           let uu____91483 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____91483 tcenv  in
         let uu____91484 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____91523 = aux rest  in
                 (match uu____91523 with
                  | (out,rest1) ->
                      let t =
                        let uu____91551 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____91551 with
                        | FStar_Pervasives_Native.Some uu____91554 ->
                            let uu____91555 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____91555
                              x.FStar_Syntax_Syntax.sort
                        | uu____91556 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____91560 =
                        let uu____91563 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___2344_91566 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2344_91566.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2344_91566.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____91563 :: out  in
                      (uu____91560, rest1))
             | uu____91571 -> ([], bindings)  in
           let uu____91578 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____91578 with
           | (closing,bindings) ->
               let uu____91605 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____91605, bindings)
            in
         match uu____91484 with
         | (q1,bindings) ->
             let uu____91636 = encode_env_bindings env bindings  in
             (match uu____91636 with
              | (env_decls,env1) ->
                  ((let uu____91658 =
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
                    if uu____91658
                    then
                      let uu____91665 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____91665
                    else ());
                   (let uu____91670 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____91670 with
                    | (phi,qdecls) ->
                        let uu____91691 =
                          let uu____91696 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____91696 phi
                           in
                        (match uu____91691 with
                         | (labels,phi1) ->
                             let uu____91713 = encode_labels labels  in
                             (match uu____91713 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____91749 =
                                      FStar_Options.log_queries ()  in
                                    if uu____91749
                                    then
                                      let uu____91754 =
                                        let uu____91755 =
                                          let uu____91757 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____91757
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____91755
                                         in
                                      [uu____91754]
                                    else []  in
                                  let query_prelude =
                                    let uu____91765 =
                                      let uu____91766 =
                                        let uu____91767 =
                                          let uu____91770 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____91777 =
                                            let uu____91780 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____91780
                                             in
                                          FStar_List.append uu____91770
                                            uu____91777
                                           in
                                        FStar_List.append env_decls
                                          uu____91767
                                         in
                                      FStar_All.pipe_right uu____91766
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____91765
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____91790 =
                                      let uu____91798 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____91799 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____91798,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____91799)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____91790
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
  