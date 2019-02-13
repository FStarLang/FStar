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
  let uu____136 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____136 with
  | (asym,a) ->
      let uu____147 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____147 with
       | (xsym,x) ->
           let uu____158 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____158 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____236 =
                      let uu____248 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____248, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____236  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____268 =
                      let uu____276 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____276)  in
                    FStar_SMTEncoding_Util.mkApp uu____268  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____295 =
                    let uu____298 =
                      let uu____301 =
                        let uu____304 =
                          let uu____305 =
                            let uu____313 =
                              let uu____314 =
                                let uu____325 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____325)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____314
                               in
                            (uu____313, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____305  in
                        let uu____337 =
                          let uu____340 =
                            let uu____341 =
                              let uu____349 =
                                let uu____350 =
                                  let uu____361 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____361)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____350
                                 in
                              (uu____349,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____341  in
                          [uu____340]  in
                        uu____304 :: uu____337  in
                      xtok_decl :: uu____301  in
                    xname_decl :: uu____298  in
                  (xtok1, (FStar_List.length vars), uu____295)  in
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
                  let uu____531 =
                    let uu____552 =
                      let uu____571 =
                        let uu____572 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____572
                         in
                      quant axy uu____571  in
                    (FStar_Parser_Const.op_Eq, uu____552)  in
                  let uu____589 =
                    let uu____612 =
                      let uu____633 =
                        let uu____652 =
                          let uu____653 =
                            let uu____654 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____654  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____653
                           in
                        quant axy uu____652  in
                      (FStar_Parser_Const.op_notEq, uu____633)  in
                    let uu____671 =
                      let uu____694 =
                        let uu____715 =
                          let uu____734 =
                            let uu____735 =
                              let uu____736 =
                                let uu____741 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____742 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____741, uu____742)  in
                              FStar_SMTEncoding_Util.mkLT uu____736  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____735
                             in
                          quant xy uu____734  in
                        (FStar_Parser_Const.op_LT, uu____715)  in
                      let uu____759 =
                        let uu____782 =
                          let uu____803 =
                            let uu____822 =
                              let uu____823 =
                                let uu____824 =
                                  let uu____829 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____830 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____829, uu____830)  in
                                FStar_SMTEncoding_Util.mkLTE uu____824  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____823
                               in
                            quant xy uu____822  in
                          (FStar_Parser_Const.op_LTE, uu____803)  in
                        let uu____847 =
                          let uu____870 =
                            let uu____891 =
                              let uu____910 =
                                let uu____911 =
                                  let uu____912 =
                                    let uu____917 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____918 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____917, uu____918)  in
                                  FStar_SMTEncoding_Util.mkGT uu____912  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____911
                                 in
                              quant xy uu____910  in
                            (FStar_Parser_Const.op_GT, uu____891)  in
                          let uu____935 =
                            let uu____958 =
                              let uu____979 =
                                let uu____998 =
                                  let uu____999 =
                                    let uu____1000 =
                                      let uu____1005 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1006 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1005, uu____1006)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1000
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____999
                                   in
                                quant xy uu____998  in
                              (FStar_Parser_Const.op_GTE, uu____979)  in
                            let uu____1023 =
                              let uu____1046 =
                                let uu____1067 =
                                  let uu____1086 =
                                    let uu____1087 =
                                      let uu____1088 =
                                        let uu____1093 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1094 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1093, uu____1094)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1088
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1087
                                     in
                                  quant xy uu____1086  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1067)
                                 in
                              let uu____1111 =
                                let uu____1134 =
                                  let uu____1155 =
                                    let uu____1174 =
                                      let uu____1175 =
                                        let uu____1176 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1176
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1175
                                       in
                                    quant qx uu____1174  in
                                  (FStar_Parser_Const.op_Minus, uu____1155)
                                   in
                                let uu____1193 =
                                  let uu____1216 =
                                    let uu____1237 =
                                      let uu____1256 =
                                        let uu____1257 =
                                          let uu____1258 =
                                            let uu____1263 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1264 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1263, uu____1264)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1258
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1257
                                         in
                                      quant xy uu____1256  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1237)
                                     in
                                  let uu____1281 =
                                    let uu____1304 =
                                      let uu____1325 =
                                        let uu____1344 =
                                          let uu____1345 =
                                            let uu____1346 =
                                              let uu____1351 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1352 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1351, uu____1352)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1346
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1345
                                           in
                                        quant xy uu____1344  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1325)
                                       in
                                    let uu____1369 =
                                      let uu____1392 =
                                        let uu____1413 =
                                          let uu____1432 =
                                            let uu____1433 =
                                              let uu____1434 =
                                                let uu____1439 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1440 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1439, uu____1440)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1434
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1433
                                             in
                                          quant xy uu____1432  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1413)
                                         in
                                      let uu____1457 =
                                        let uu____1480 =
                                          let uu____1501 =
                                            let uu____1520 =
                                              let uu____1521 =
                                                let uu____1522 =
                                                  let uu____1527 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1528 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1527, uu____1528)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1522
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1521
                                               in
                                            quant xy uu____1520  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1501)
                                           in
                                        let uu____1545 =
                                          let uu____1568 =
                                            let uu____1589 =
                                              let uu____1608 =
                                                let uu____1609 =
                                                  let uu____1610 =
                                                    let uu____1615 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1616 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1615, uu____1616)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1610
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1609
                                                 in
                                              quant xy uu____1608  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1589)
                                             in
                                          let uu____1633 =
                                            let uu____1656 =
                                              let uu____1677 =
                                                let uu____1696 =
                                                  let uu____1697 =
                                                    let uu____1698 =
                                                      let uu____1703 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1704 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1703,
                                                        uu____1704)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1698
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1697
                                                   in
                                                quant xy uu____1696  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1677)
                                               in
                                            let uu____1721 =
                                              let uu____1744 =
                                                let uu____1765 =
                                                  let uu____1784 =
                                                    let uu____1785 =
                                                      let uu____1786 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1786
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1785
                                                     in
                                                  quant qx uu____1784  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1765)
                                                 in
                                              [uu____1744]  in
                                            uu____1656 :: uu____1721  in
                                          uu____1568 :: uu____1633  in
                                        uu____1480 :: uu____1545  in
                                      uu____1392 :: uu____1457  in
                                    uu____1304 :: uu____1369  in
                                  uu____1216 :: uu____1281  in
                                uu____1134 :: uu____1193  in
                              uu____1046 :: uu____1111  in
                            uu____958 :: uu____1023  in
                          uu____870 :: uu____935  in
                        uu____782 :: uu____847  in
                      uu____694 :: uu____759  in
                    uu____612 :: uu____671  in
                  uu____531 :: uu____589  in
                let mk1 l v1 =
                  let uu____2145 =
                    let uu____2157 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2247  ->
                              match uu____2247 with
                              | (l',uu____2268) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2157
                      (FStar_Option.map
                         (fun uu____2367  ->
                            match uu____2367 with
                            | (uu____2395,b) ->
                                let uu____2429 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2429 v1))
                     in
                  FStar_All.pipe_right uu____2145 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2512  ->
                          match uu____2512 with
                          | (l',uu____2533) -> FStar_Ident.lid_equals l l'))
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
          let uu____2607 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2607 with
          | (xxsym,xx) ->
              let uu____2618 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2618 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2634 =
                     let uu____2642 =
                       let uu____2643 =
                         let uu____2654 =
                           let uu____2655 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____2665 =
                             let uu____2676 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____2676 :: vars  in
                           uu____2655 :: uu____2665  in
                         let uu____2702 =
                           let uu____2703 =
                             let uu____2708 =
                               let uu____2709 =
                                 let uu____2714 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2714)  in
                               FStar_SMTEncoding_Util.mkEq uu____2709  in
                             (xx_has_type, uu____2708)  in
                           FStar_SMTEncoding_Util.mkImp uu____2703  in
                         ([[xx_has_type]], uu____2654, uu____2702)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____2643  in
                     let uu____2727 =
                       let uu____2729 =
                         let uu____2731 =
                           let uu____2733 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2733  in
                         Prims.strcat module_name uu____2731  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2729
                        in
                     (uu____2642, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2727)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2634)
  
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
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____2786 =
      let uu____2787 =
        let uu____2795 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2795, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2787  in
    let uu____2800 =
      let uu____2803 =
        let uu____2804 =
          let uu____2812 =
            let uu____2813 =
              let uu____2824 =
                let uu____2825 =
                  let uu____2830 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2830)  in
                FStar_SMTEncoding_Util.mkImp uu____2825  in
              ([[typing_pred]], [xx], uu____2824)  in
            let uu____2855 =
              let uu____2870 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2870  in
            uu____2855 uu____2813  in
          (uu____2812, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2804  in
      [uu____2803]  in
    uu____2786 :: uu____2800  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2898 =
      let uu____2899 =
        let uu____2907 =
          let uu____2908 = FStar_TypeChecker_Env.get_range env  in
          let uu____2909 =
            let uu____2920 =
              let uu____2925 =
                let uu____2928 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2928]  in
              [uu____2925]  in
            let uu____2933 =
              let uu____2934 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2934 tt  in
            (uu____2920, [bb], uu____2933)  in
          FStar_SMTEncoding_Term.mkForall uu____2908 uu____2909  in
        (uu____2907, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2899  in
    let uu____2959 =
      let uu____2962 =
        let uu____2963 =
          let uu____2971 =
            let uu____2972 =
              let uu____2983 =
                let uu____2984 =
                  let uu____2989 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2989)  in
                FStar_SMTEncoding_Util.mkImp uu____2984  in
              ([[typing_pred]], [xx], uu____2983)  in
            let uu____3016 =
              let uu____3031 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3031  in
            uu____3016 uu____2972  in
          (uu____2971, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2963  in
      [uu____2962]  in
    uu____2898 :: uu____2959  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3055 =
        let uu____3056 =
          let uu____3062 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____3062, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____3056  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3055  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3076 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3076  in
    let uu____3081 =
      let uu____3082 =
        let uu____3090 =
          let uu____3091 = FStar_TypeChecker_Env.get_range env  in
          let uu____3092 =
            let uu____3103 =
              let uu____3108 =
                let uu____3111 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3111]  in
              [uu____3108]  in
            let uu____3116 =
              let uu____3117 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3117 tt  in
            (uu____3103, [bb], uu____3116)  in
          FStar_SMTEncoding_Term.mkForall uu____3091 uu____3092  in
        (uu____3090, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3082  in
    let uu____3142 =
      let uu____3145 =
        let uu____3146 =
          let uu____3154 =
            let uu____3155 =
              let uu____3166 =
                let uu____3167 =
                  let uu____3172 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3172)  in
                FStar_SMTEncoding_Util.mkImp uu____3167  in
              ([[typing_pred]], [xx], uu____3166)  in
            let uu____3199 =
              let uu____3214 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3214  in
            uu____3199 uu____3155  in
          (uu____3154, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3146  in
      let uu____3219 =
        let uu____3222 =
          let uu____3223 =
            let uu____3231 =
              let uu____3232 =
                let uu____3243 =
                  let uu____3244 =
                    let uu____3249 =
                      let uu____3250 =
                        let uu____3253 =
                          let uu____3256 =
                            let uu____3259 =
                              let uu____3260 =
                                let uu____3265 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3266 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3265, uu____3266)  in
                              FStar_SMTEncoding_Util.mkGT uu____3260  in
                            let uu____3268 =
                              let uu____3271 =
                                let uu____3272 =
                                  let uu____3277 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3278 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3277, uu____3278)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3272  in
                              let uu____3280 =
                                let uu____3283 =
                                  let uu____3284 =
                                    let uu____3289 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3290 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3289, uu____3290)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3284  in
                                [uu____3283]  in
                              uu____3271 :: uu____3280  in
                            uu____3259 :: uu____3268  in
                          typing_pred_y :: uu____3256  in
                        typing_pred :: uu____3253  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3250  in
                    (uu____3249, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3244  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3243)
                 in
              let uu____3323 =
                let uu____3338 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3338  in
              uu____3323 uu____3232  in
            (uu____3231,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3223  in
        [uu____3222]  in
      uu____3145 :: uu____3219  in
    uu____3081 :: uu____3142  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3366 =
      let uu____3367 =
        let uu____3375 =
          let uu____3376 = FStar_TypeChecker_Env.get_range env  in
          let uu____3377 =
            let uu____3388 =
              let uu____3393 =
                let uu____3396 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3396]  in
              [uu____3393]  in
            let uu____3401 =
              let uu____3402 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3402 tt  in
            (uu____3388, [bb], uu____3401)  in
          FStar_SMTEncoding_Term.mkForall uu____3376 uu____3377  in
        (uu____3375, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3367  in
    let uu____3427 =
      let uu____3430 =
        let uu____3431 =
          let uu____3439 =
            let uu____3440 =
              let uu____3451 =
                let uu____3452 =
                  let uu____3457 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3457)  in
                FStar_SMTEncoding_Util.mkImp uu____3452  in
              ([[typing_pred]], [xx], uu____3451)  in
            let uu____3484 =
              let uu____3499 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3499  in
            uu____3484 uu____3440  in
          (uu____3439, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3431  in
      [uu____3430]  in
    uu____3366 :: uu____3427  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3527 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3527]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3555 =
      let uu____3556 =
        let uu____3564 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3564, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3556  in
    [uu____3555]  in
  let mk_and_interp env conj uu____3585 =
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
    let uu____3614 =
      let uu____3615 =
        let uu____3623 =
          let uu____3624 = FStar_TypeChecker_Env.get_range env  in
          let uu____3625 =
            let uu____3636 =
              let uu____3637 =
                let uu____3642 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3642, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3637  in
            ([[l_and_a_b]], [aa; bb], uu____3636)  in
          FStar_SMTEncoding_Term.mkForall uu____3624 uu____3625  in
        (uu____3623, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3615  in
    [uu____3614]  in
  let mk_or_interp env disj uu____3695 =
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
    let uu____3724 =
      let uu____3725 =
        let uu____3733 =
          let uu____3734 = FStar_TypeChecker_Env.get_range env  in
          let uu____3735 =
            let uu____3746 =
              let uu____3747 =
                let uu____3752 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3752, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3747  in
            ([[l_or_a_b]], [aa; bb], uu____3746)  in
          FStar_SMTEncoding_Term.mkForall uu____3734 uu____3735  in
        (uu____3733, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3725  in
    [uu____3724]  in
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
    let uu____3828 =
      let uu____3829 =
        let uu____3837 =
          let uu____3838 = FStar_TypeChecker_Env.get_range env  in
          let uu____3839 =
            let uu____3850 =
              let uu____3851 =
                let uu____3856 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3856, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3851  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3850)  in
          FStar_SMTEncoding_Term.mkForall uu____3838 uu____3839  in
        (uu____3837, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3829  in
    [uu____3828]  in
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
    let uu____3944 =
      let uu____3945 =
        let uu____3953 =
          let uu____3954 = FStar_TypeChecker_Env.get_range env  in
          let uu____3955 =
            let uu____3966 =
              let uu____3967 =
                let uu____3972 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3972, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3967  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3966)  in
          FStar_SMTEncoding_Term.mkForall uu____3954 uu____3955  in
        (uu____3953, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3945  in
    [uu____3944]  in
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
    let uu____4070 =
      let uu____4071 =
        let uu____4079 =
          let uu____4080 = FStar_TypeChecker_Env.get_range env  in
          let uu____4081 =
            let uu____4092 =
              let uu____4093 =
                let uu____4098 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____4098, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4093  in
            ([[l_imp_a_b]], [aa; bb], uu____4092)  in
          FStar_SMTEncoding_Term.mkForall uu____4080 uu____4081  in
        (uu____4079, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4071  in
    [uu____4070]  in
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
    let uu____4180 =
      let uu____4181 =
        let uu____4189 =
          let uu____4190 = FStar_TypeChecker_Env.get_range env  in
          let uu____4191 =
            let uu____4202 =
              let uu____4203 =
                let uu____4208 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4208, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4203  in
            ([[l_iff_a_b]], [aa; bb], uu____4202)  in
          FStar_SMTEncoding_Term.mkForall uu____4190 uu____4191  in
        (uu____4189, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4181  in
    [uu____4180]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4277 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4277  in
    let uu____4282 =
      let uu____4283 =
        let uu____4291 =
          let uu____4292 = FStar_TypeChecker_Env.get_range env  in
          let uu____4293 =
            let uu____4304 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4304)  in
          FStar_SMTEncoding_Term.mkForall uu____4292 uu____4293  in
        (uu____4291, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4283  in
    [uu____4282]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4355 =
      let uu____4356 =
        let uu____4364 =
          let uu____4365 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4365 range_ty  in
        let uu____4366 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4364, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4366)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4356  in
    [uu____4355]  in
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
        let uu____4410 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4410 x1 t  in
      let uu____4412 = FStar_TypeChecker_Env.get_range env  in
      let uu____4413 =
        let uu____4424 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4424)  in
      FStar_SMTEncoding_Term.mkForall uu____4412 uu____4413  in
    let uu____4449 =
      let uu____4450 =
        let uu____4458 =
          let uu____4459 = FStar_TypeChecker_Env.get_range env  in
          let uu____4460 =
            let uu____4471 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4471)  in
          FStar_SMTEncoding_Term.mkForall uu____4459 uu____4460  in
        (uu____4458,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4450  in
    [uu____4449]  in
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
    let uu____4530 =
      let uu____4531 =
        let uu____4539 =
          let uu____4540 = FStar_TypeChecker_Env.get_range env  in
          let uu____4541 =
            let uu____4557 =
              let uu____4558 =
                let uu____4563 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4564 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4563, uu____4564)  in
              FStar_SMTEncoding_Util.mkAnd uu____4558  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4557)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4540 uu____4541  in
        (uu____4539,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4531  in
    [uu____4530]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
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
          let uu____5094 =
            FStar_Util.find_opt
              (fun uu____5132  ->
                 match uu____5132 with
                 | (l,uu____5148) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5094 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____5191,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5252 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5252 with
        | (form,decls) ->
            let uu____5261 =
              let uu____5264 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5264]  in
            FStar_List.append decls uu____5261
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list *
                FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____5317 =
                ((let uu____5321 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5321) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5317
              then
                let arg_sorts =
                  let uu____5335 =
                    let uu____5336 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5336.FStar_Syntax_Syntax.n  in
                  match uu____5335 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5342) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5380  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5387 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5389 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5389 with
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
                    ([d; dd], env1)
              else
                (let uu____5431 = prims.is lid  in
                 if uu____5431
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5442 = prims.mk lid vname  in
                   match uu____5442 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5476 =
                      let uu____5495 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5495 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5523 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5523
                            then
                              let uu____5528 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___384_5531 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___384_5531.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___384_5531.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___384_5531.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___384_5531.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___384_5531.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___384_5531.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___384_5531.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___384_5531.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___384_5531.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___384_5531.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___384_5531.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___384_5531.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___384_5531.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___384_5531.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___384_5531.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___384_5531.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___384_5531.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___384_5531.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___384_5531.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___384_5531.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___384_5531.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___384_5531.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___384_5531.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___384_5531.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___384_5531.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___384_5531.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___384_5531.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___384_5531.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___384_5531.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___384_5531.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___384_5531.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___384_5531.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___384_5531.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___384_5531.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___384_5531.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___384_5531.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___384_5531.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___384_5531.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___384_5531.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___384_5531.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___384_5531.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___384_5531.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5528
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5554 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5554)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5476 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___374_5662  ->
                                  match uu___374_5662 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____5666 = FStar_Util.prefix vars
                                         in
                                      (match uu____5666 with
                                       | (uu____5699,xxv) ->
                                           let xx =
                                             let uu____5738 =
                                               let uu____5739 =
                                                 let uu____5745 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____5745,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____5739
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____5738
                                              in
                                           let uu____5748 =
                                             let uu____5749 =
                                               let uu____5757 =
                                                 let uu____5758 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5759 =
                                                   let uu____5770 =
                                                     let uu____5771 =
                                                       let uu____5776 =
                                                         let uu____5777 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____5777
                                                          in
                                                       (vapp, uu____5776)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____5771
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5770)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5758 uu____5759
                                                  in
                                               (uu____5757,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.strcat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5749
                                              in
                                           [uu____5748])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____5792 = FStar_Util.prefix vars
                                         in
                                      (match uu____5792 with
                                       | (uu____5825,xxv) ->
                                           let xx =
                                             let uu____5864 =
                                               let uu____5865 =
                                                 let uu____5871 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____5871,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____5865
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____5864
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
                                           let uu____5882 =
                                             let uu____5883 =
                                               let uu____5891 =
                                                 let uu____5892 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5893 =
                                                   let uu____5904 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5904)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5892 uu____5893
                                                  in
                                               (uu____5891,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.strcat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5883
                                              in
                                           [uu____5882])
                                  | uu____5917 -> []))
                           in
                        let uu____5918 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____5918 with
                         | (vars,guards,env',decls1,uu____5945) ->
                             let uu____5958 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____5971 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____5971, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____5975 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____5975 with
                                    | (g,ds) ->
                                        let uu____5988 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____5988,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____5958 with
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
                                  let should_thunk uu____6013 =
                                    let is_type1 t =
                                      let uu____6021 =
                                        let uu____6022 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6022.FStar_Syntax_Syntax.n  in
                                      match uu____6021 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____6026 -> true
                                      | uu____6028 -> false  in
                                    let is_squash1 t =
                                      let uu____6037 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____6037 with
                                      | (head1,uu____6056) ->
                                          let uu____6081 =
                                            let uu____6082 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____6082.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6081 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____6087;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____6088;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____6090;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____6091;_};_},uu____6092)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____6100 -> false)
                                       in
                                    ((lid.FStar_Ident.nsstr <> "Prims") &&
                                       (let uu____6105 =
                                          FStar_All.pipe_right quals
                                            (FStar_List.contains
                                               FStar_Syntax_Syntax.Logic)
                                           in
                                        Prims.op_Negation uu____6105))
                                      &&
                                      (let uu____6111 = is_squash1 t_norm  in
                                       Prims.op_Negation uu____6111)
                                     in
                                  let uu____6113 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____6172 -> (false, vars)  in
                                  (match uu____6113 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____6224 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____6224 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____6262 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____6271 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____6271
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____6282 ->
                                                  let uu____6291 =
                                                    let uu____6299 =
                                                      get_vtok ()  in
                                                    (uu____6299, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6291
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____6306 =
                                                let uu____6314 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____6314)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____6306
                                               in
                                            let uu____6328 =
                                              let vname_decl =
                                                let uu____6336 =
                                                  let uu____6348 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____6348,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____6336
                                                 in
                                              let uu____6359 =
                                                let env2 =
                                                  let uu___385_6365 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.cache
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.cache);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___385_6365.FStar_SMTEncoding_Env.encoding_quantifier)
                                                  }  in
                                                let uu____6366 =
                                                  let uu____6368 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____6368
                                                   in
                                                if uu____6366
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____6359 with
                                              | (tok_typing,decls2) ->
                                                  let uu____6385 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____6411 =
                                                          let uu____6412 =
                                                            let uu____6415 =
                                                              let uu____6416
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____6416
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____6415
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____6412
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [tok_typing1]),
                                                          uu____6411)
                                                    | uu____6426 when thunked
                                                        ->
                                                        let uu____6437 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____6437
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____6452
                                                                 =
                                                                 let uu____6460
                                                                   =
                                                                   let uu____6463
                                                                    =
                                                                    let uu____6466
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____6466]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____6463
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____6460)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____6452
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____6474 =
                                                               let uu____6482
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____6482,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.strcat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____6474
                                                              in
                                                           ((FStar_List.append
                                                               decls2
                                                               [intro_ambient1]),
                                                             env1))
                                                    | uu____6489 ->
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
                                                          let uu____6513 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____6514 =
                                                            let uu____6525 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____6525)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____6513
                                                            uu____6514
                                                           in
                                                        let name_tok_corr =
                                                          let uu____6535 =
                                                            let uu____6543 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____6543,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____6535
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
                                                            let uu____6554 =
                                                              let uu____6555
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____6555]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____6554
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____6582 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6583 =
                                                              let uu____6594
                                                                =
                                                                let uu____6595
                                                                  =
                                                                  let uu____6600
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____6601
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____6600,
                                                                    uu____6601)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____6595
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____6594)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6582
                                                              uu____6583
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [vtok_decl;
                                                            name_tok_corr;
                                                            tok_typing1]),
                                                          env1)
                                                     in
                                                  (match uu____6385 with
                                                   | (tok_decl,env2) ->
                                                       ((vname_decl ::
                                                         tok_decl), env2))
                                               in
                                            (match uu____6328 with
                                             | (decls2,env2) ->
                                                 let uu____6658 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____6668 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____6668 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____6683 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____6683, decls)
                                                    in
                                                 (match uu____6658 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____6700 =
                                                          let uu____6708 =
                                                            let uu____6709 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6710 =
                                                              let uu____6721
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____6721)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6709
                                                              uu____6710
                                                             in
                                                          (uu____6708,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6700
                                                         in
                                                      let freshness =
                                                        let uu____6737 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____6737
                                                        then
                                                          let uu____6745 =
                                                            let uu____6746 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6747 =
                                                              let uu____6760
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____6767
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____6760,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____6767)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____6746
                                                              uu____6747
                                                             in
                                                          let uu____6773 =
                                                            let uu____6776 =
                                                              let uu____6777
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____6777
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____6776]  in
                                                          uu____6745 ::
                                                            uu____6773
                                                        else []  in
                                                      let g =
                                                        let uu____6783 =
                                                          let uu____6786 =
                                                            let uu____6789 =
                                                              let uu____6792
                                                                =
                                                                let uu____6795
                                                                  =
                                                                  mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1
                                                                   in
                                                                typingAx ::
                                                                  uu____6795
                                                                 in
                                                              FStar_List.append
                                                                freshness
                                                                uu____6792
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____6789
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6786
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____6783
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl
            Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____6833 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6833 with
          | FStar_Pervasives_Native.None  ->
              let uu____6844 = encode_free_var false env x t t_norm []  in
              (match uu____6844 with
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
            (FStar_SMTEncoding_Term.decl Prims.list *
              FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____6915 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6915 with
            | (decls,env1) ->
                let uu____6934 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6934
                then
                  let uu____6943 =
                    let uu____6946 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6946  in
                  (uu____6943, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____7006  ->
                fun lb  ->
                  match uu____7006 with
                  | (decls,env1) ->
                      let uu____7026 =
                        let uu____7033 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7033
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7026 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7066 = FStar_Syntax_Util.head_and_args t  in
    match uu____7066 with
    | (hd1,args) ->
        let uu____7110 =
          let uu____7111 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7111.FStar_Syntax_Syntax.n  in
        (match uu____7110 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7117,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7141 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7152 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___386_7160 = en  in
    let uu____7161 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___386_7160.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___386_7160.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___386_7160.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___386_7160.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___386_7160.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7161;
      FStar_SMTEncoding_Env.nolabels =
        (uu___386_7160.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___386_7160.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___386_7160.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___386_7160.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___386_7160.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7193  ->
      fun quals  ->
        match uu____7193 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7300 = FStar_Util.first_N nbinders formals  in
              match uu____7300 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7401  ->
                         fun uu____7402  ->
                           match (uu____7401, uu____7402) with
                           | ((formal,uu____7428),(binder,uu____7430)) ->
                               let uu____7451 =
                                 let uu____7458 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7458)  in
                               FStar_Syntax_Syntax.NT uu____7451) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7472 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7513  ->
                              match uu____7513 with
                              | (x,i) ->
                                  let uu____7532 =
                                    let uu___387_7533 = x  in
                                    let uu____7534 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___387_7533.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___387_7533.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7534
                                    }  in
                                  (uu____7532, i)))
                       in
                    FStar_All.pipe_right uu____7472
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7558 =
                      let uu____7563 = FStar_Syntax_Subst.compress body  in
                      let uu____7564 =
                        let uu____7565 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7565
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7563 uu____7564
                       in
                    uu____7558 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___388_7616 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___388_7616.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___388_7616.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___388_7616.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___388_7616.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___388_7616.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___388_7616.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___388_7616.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___388_7616.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___388_7616.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___388_7616.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___388_7616.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___388_7616.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___388_7616.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___388_7616.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___388_7616.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___388_7616.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___388_7616.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___388_7616.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___388_7616.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___388_7616.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___388_7616.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___388_7616.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___388_7616.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___388_7616.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___388_7616.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___388_7616.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___388_7616.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___388_7616.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___388_7616.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___388_7616.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___388_7616.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___388_7616.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___388_7616.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___388_7616.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___388_7616.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___388_7616.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___388_7616.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___388_7616.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___388_7616.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___388_7616.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___388_7616.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___388_7616.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7688  ->
                       fun uu____7689  ->
                         match (uu____7688, uu____7689) with
                         | ((x,uu____7715),(b,uu____7717)) ->
                             let uu____7738 =
                               let uu____7745 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7745)  in
                             FStar_Syntax_Syntax.NT uu____7738) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7770 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7770
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7799 ->
                    let uu____7806 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7806
                | uu____7807 when Prims.op_Negation norm1 ->
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
                | uu____7810 ->
                    let uu____7811 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7811)
                 in
              let aux t1 e1 =
                let uu____7853 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7853 with
                | (binders,body,lopt) ->
                    let uu____7885 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7901 -> arrow_formals_comp_norm false t1  in
                    (match uu____7885 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7935 =
                           if nformals < nbinders
                           then
                             let uu____7979 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7979 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____8063 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____8063)
                           else
                             if nformals > nbinders
                             then
                               (let uu____8103 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____8103 with
                                | (binders1,body1) ->
                                    let uu____8156 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____8156))
                             else
                               (let uu____8169 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____8169))
                            in
                         (match uu____7935 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____8229 = aux t e  in
              match uu____8229 with
              | (binders,body,comp) ->
                  let uu____8275 =
                    let uu____8286 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____8286
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____8301 = aux comp1 body1  in
                      match uu____8301 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____8275 with
                   | (binders1,body1,comp1) ->
                       let uu____8384 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____8384, comp1))
               in
            (try
               (fun uu___390_8411  ->
                  match () with
                  | () ->
                      let uu____8418 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8418
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8434 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8497  ->
                                   fun lb  ->
                                     match uu____8497 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8552 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8552
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8558 =
                                             let uu____8567 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8567
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8558 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8434 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____8708;
                                    FStar_Syntax_Syntax.lbeff = uu____8709;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8711;
                                    FStar_Syntax_Syntax.lbpos = uu____8712;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8736 =
                                     let uu____8743 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8743 with
                                     | (tcenv',uu____8759,e_t) ->
                                         let uu____8765 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8776 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8765 with
                                          | (e1,t_norm1) ->
                                              ((let uu___391_8793 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___391_8793.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8736 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8803 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____8803 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8823 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8823
                                               then
                                                 let uu____8828 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8831 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8828 uu____8831
                                               else ());
                                              (let uu____8836 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8836 with
                                               | (vars,_guards,env'1,binder_decls,uu____8863)
                                                   ->
                                                   let uu____8876 =
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
                                                         let uu____8893 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____8893
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____8915 =
                                                          let uu____8916 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____8917 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____8916 fvb
                                                            uu____8917
                                                           in
                                                        (vars, uu____8915))
                                                      in
                                                   (match uu____8876 with
                                                    | (vars1,app) ->
                                                        let uu____8928 =
                                                          let is_logical =
                                                            let uu____8941 =
                                                              let uu____8942
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____8942.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____8941
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____8948 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____8952 =
                                                              let uu____8953
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8953
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____8952
                                                              (fun lid  ->
                                                                 let uu____8962
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____8962
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____8963 =
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
                                                          if uu____8963
                                                          then
                                                            let uu____8979 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____8980 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app, uu____8979,
                                                              uu____8980)
                                                          else
                                                            (let uu____8991 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____8991))
                                                           in
                                                        (match uu____8928
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____9015
                                                                 =
                                                                 let uu____9023
                                                                   =
                                                                   let uu____9024
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____9025
                                                                    =
                                                                    let uu____9036
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____9036)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____9024
                                                                    uu____9025
                                                                    in
                                                                 let uu____9045
                                                                   =
                                                                   let uu____9046
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9046
                                                                    in
                                                                 (uu____9023,
                                                                   uu____9045,
                                                                   (Prims.strcat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____9015
                                                                in
                                                             let uu____9052 =
                                                               let uu____9055
                                                                 =
                                                                 let uu____9058
                                                                   =
                                                                   let uu____9061
                                                                    =
                                                                    let uu____9064
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    FStar_List.append
                                                                    [eqn]
                                                                    uu____9064
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____9061
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____9058
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____9055
                                                                in
                                                             (uu____9052,
                                                               env2)))))))
                               | uu____9069 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9129 =
                                   let uu____9135 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       "fuel"
                                      in
                                   (uu____9135,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____9129  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9141 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9194  ->
                                         fun fvb  ->
                                           match uu____9194 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9249 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9249
                                                  in
                                               let gtok =
                                                 let uu____9253 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9253
                                                  in
                                               let env4 =
                                                 let uu____9256 =
                                                   let uu____9259 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9259
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9256
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9141 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9386
                                     t_norm uu____9388 =
                                     match (uu____9386, uu____9388) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9420;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9421;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9423;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9424;_})
                                         ->
                                         let uu____9451 =
                                           let uu____9458 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9458 with
                                           | (tcenv',uu____9474,e_t) ->
                                               let uu____9480 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9491 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9480 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___392_9508 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___392_9508.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9451 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9523 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9523
                                                then
                                                  let uu____9528 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9530 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9532 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9528 uu____9530
                                                    uu____9532
                                                else ());
                                               (let uu____9537 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____9537 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9566 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9566 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9590 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9590
                                                           then
                                                             let uu____9595 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9597 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9600 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9602 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9595
                                                               uu____9597
                                                               uu____9600
                                                               uu____9602
                                                           else ());
                                                          (let uu____9607 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9607
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9638)
                                                               ->
                                                               let uu____9651
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9664
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9664,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9668
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9668
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9681
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9681,
                                                                    decls0))
                                                                  in
                                                               (match uu____9651
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
                                                                    let uu____9704
                                                                    =
                                                                    let uu____9716
                                                                    =
                                                                    let uu____9719
                                                                    =
                                                                    let uu____9722
                                                                    =
                                                                    let uu____9725
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9725
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____9722
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9719
                                                                     in
                                                                    (g,
                                                                    uu____9716,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9704
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
                                                                    let uu____9755
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9755
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
                                                                    let uu____9770
                                                                    =
                                                                    let uu____9773
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9773
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9770
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9779
                                                                    =
                                                                    let uu____9782
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9782
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9779
                                                                     in
                                                                    let uu____9787
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9787
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9805
                                                                    =
                                                                    let uu____9813
                                                                    =
                                                                    let uu____9814
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9815
                                                                    =
                                                                    let uu____9831
                                                                    =
                                                                    let uu____9832
                                                                    =
                                                                    let uu____9837
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9837)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9832
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9831)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9814
                                                                    uu____9815
                                                                     in
                                                                    let uu____9851
                                                                    =
                                                                    let uu____9852
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9852
                                                                     in
                                                                    (uu____9813,
                                                                    uu____9851,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9805
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9859
                                                                    =
                                                                    let uu____9867
                                                                    =
                                                                    let uu____9868
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9869
                                                                    =
                                                                    let uu____9880
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9880)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9868
                                                                    uu____9869
                                                                     in
                                                                    (uu____9867,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9859
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9894
                                                                    =
                                                                    let uu____9902
                                                                    =
                                                                    let uu____9903
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9904
                                                                    =
                                                                    let uu____9915
                                                                    =
                                                                    let uu____9916
                                                                    =
                                                                    let uu____9921
                                                                    =
                                                                    let uu____9922
                                                                    =
                                                                    let uu____9925
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9925
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9922
                                                                     in
                                                                    (gsapp,
                                                                    uu____9921)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9916
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9915)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9903
                                                                    uu____9904
                                                                     in
                                                                    (uu____9902,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9894
                                                                     in
                                                                    let uu____9939
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
                                                                    let uu____9951
                                                                    =
                                                                    let uu____9952
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____9952
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9951
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9954
                                                                    =
                                                                    let uu____9962
                                                                    =
                                                                    let uu____9963
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9964
                                                                    =
                                                                    let uu____9975
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9975)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9963
                                                                    uu____9964
                                                                     in
                                                                    (uu____9962,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9954
                                                                     in
                                                                    let uu____9988
                                                                    =
                                                                    let uu____9997
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____9997
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10012
                                                                    =
                                                                    let uu____10015
                                                                    =
                                                                    let uu____10016
                                                                    =
                                                                    let uu____10024
                                                                    =
                                                                    let uu____10025
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10026
                                                                    =
                                                                    let uu____10037
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10037)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10025
                                                                    uu____10026
                                                                     in
                                                                    (uu____10024,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10016
                                                                     in
                                                                    [uu____10015]
                                                                     in
                                                                    (d3,
                                                                    uu____10012)
                                                                     in
                                                                    match uu____9988
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9939
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    (FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                    env02))))))))))
                                      in
                                   let uu____10100 =
                                     let uu____10113 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10176  ->
                                          fun uu____10177  ->
                                            match (uu____10176, uu____10177)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10302 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10302 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10113
                                      in
                                   (match uu____10100 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10375 =
                                          let isDeclFun uu___375_10390 =
                                            match uu___375_10390 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10392 -> true
                                            | uu____10405 -> false  in
                                          let uu____10407 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10407
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____10375 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10447 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___376_10453  ->
                                        match uu___376_10453 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10456 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10464 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10464)))
                                in
                             if uu____10447
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___394_10486  ->
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
                   let uu____10524 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10524
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____10594 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10594 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10600 = encode_sigelt' env se  in
      match uu____10600 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10612 =
                  let uu____10613 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____10613  in
                [uu____10612]
            | uu____10616 ->
                let uu____10617 =
                  let uu____10620 =
                    let uu____10621 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10621  in
                  uu____10620 :: g  in
                let uu____10624 =
                  let uu____10627 =
                    let uu____10628 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10628  in
                  [uu____10627]  in
                FStar_List.append uu____10617 uu____10624
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____10638 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____10638
       then
         let uu____10643 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____10643
       else ());
      (let is_opaque_to_smt t =
         let uu____10655 =
           let uu____10656 = FStar_Syntax_Subst.compress t  in
           uu____10656.FStar_Syntax_Syntax.n  in
         match uu____10655 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10661)) -> s = "opaque_to_smt"
         | uu____10666 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____10675 =
           let uu____10676 = FStar_Syntax_Subst.compress t  in
           uu____10676.FStar_Syntax_Syntax.n  in
         match uu____10675 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10681)) -> s = "uninterpreted_by_smt"
         | uu____10686 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10692 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____10698 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____10710 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____10711 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10712 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____10725 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____10727 =
             let uu____10729 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____10729  in
           if uu____10727
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____10758 ->
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
                let uu____10790 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____10790 with
                | (formals,uu____10810) ->
                    let arity = FStar_List.length formals  in
                    let uu____10834 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____10834 with
                     | (aname,atok,env2) ->
                         let uu____10860 =
                           let uu____10865 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____10865 env2
                            in
                         (match uu____10860 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____10877 =
                                  let uu____10878 =
                                    let uu____10890 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____10910  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____10890,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____10878
                                   in
                                [uu____10877;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____10927 =
                                let aux uu____10973 uu____10974 =
                                  match (uu____10973, uu____10974) with
                                  | ((bv,uu____11018),(env3,acc_sorts,acc))
                                      ->
                                      let uu____11050 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____11050 with
                                       | (xxsym,xx,env4) ->
                                           let uu____11073 =
                                             let uu____11076 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____11076 :: acc_sorts  in
                                           (env4, uu____11073, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____10927 with
                               | (uu____11108,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____11124 =
                                       let uu____11132 =
                                         let uu____11133 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11134 =
                                           let uu____11145 =
                                             let uu____11146 =
                                               let uu____11151 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____11151)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____11146
                                              in
                                           ([[app]], xs_sorts, uu____11145)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11133 uu____11134
                                          in
                                       (uu____11132,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.strcat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11124
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____11166 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____11166
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____11169 =
                                       let uu____11177 =
                                         let uu____11178 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11179 =
                                           let uu____11190 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____11190)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11178 uu____11179
                                          in
                                       (uu____11177,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.strcat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11169
                                      in
                                   (env2,
                                     (FStar_List.append decls
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence]))))))
                 in
              let uu____11205 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____11205 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11231,uu____11232)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____11233 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____11233 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11255,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____11262 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___377_11268  ->
                       match uu___377_11268 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____11271 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11277 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____11280 -> false))
                in
             Prims.op_Negation uu____11262  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____11290 =
                let uu____11297 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____11297 env fv t quals  in
              match uu____11290 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____11315 =
                      FStar_SMTEncoding_Term.mk_fv
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____11315
                     in
                  let uu____11317 =
                    let uu____11318 =
                      primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                        lid tname tsym
                       in
                    FStar_List.append decls uu____11318  in
                  (uu____11317, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____11324 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____11324 with
            | (uvs,f1) ->
                let env1 =
                  let uu___395_11336 = env  in
                  let uu____11337 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___395_11336.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___395_11336.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___395_11336.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____11337;
                    FStar_SMTEncoding_Env.warn =
                      (uu___395_11336.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.cache =
                      (uu___395_11336.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___395_11336.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___395_11336.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___395_11336.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___395_11336.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___395_11336.FStar_SMTEncoding_Env.encoding_quantifier)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____11339 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____11339 with
                 | (f3,decls) ->
                     let g =
                       let uu____11353 =
                         let uu____11354 =
                           let uu____11362 =
                             let uu____11363 =
                               let uu____11365 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.format1 "Assumption: %s"
                                 uu____11365
                                in
                             FStar_Pervasives_Native.Some uu____11363  in
                           let uu____11369 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                               (Prims.strcat "assumption_" l.FStar_Ident.str)
                              in
                           (f3, uu____11362, uu____11369)  in
                         FStar_SMTEncoding_Util.mkAssume uu____11354  in
                       [uu____11353]  in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____11374) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____11388 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____11410 =
                        let uu____11413 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____11413.FStar_Syntax_Syntax.fv_name  in
                      uu____11410.FStar_Syntax_Syntax.v  in
                    let uu____11414 =
                      let uu____11416 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____11416  in
                    if uu____11414
                    then
                      let val_decl =
                        let uu___396_11448 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___396_11448.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___396_11448.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___396_11448.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____11449 = encode_sigelt' env1 val_decl  in
                      match uu____11449 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____11388 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____11485,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____11487;
                           FStar_Syntax_Syntax.lbtyp = uu____11488;
                           FStar_Syntax_Syntax.lbeff = uu____11489;
                           FStar_Syntax_Syntax.lbdef = uu____11490;
                           FStar_Syntax_Syntax.lbattrs = uu____11491;
                           FStar_Syntax_Syntax.lbpos = uu____11492;_}::[]),uu____11493)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____11512 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____11512 with
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
                  let uu____11550 =
                    let uu____11553 =
                      let uu____11554 =
                        let uu____11562 =
                          let uu____11563 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____11564 =
                            let uu____11575 =
                              let uu____11576 =
                                let uu____11581 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____11581)  in
                              FStar_SMTEncoding_Util.mkEq uu____11576  in
                            ([[b2t_x]], [xx], uu____11575)  in
                          FStar_SMTEncoding_Term.mkForall uu____11563
                            uu____11564
                           in
                        (uu____11562,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____11554  in
                    [uu____11553]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____11550
                   in
                (decls, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____11619,uu____11620) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___378_11630  ->
                   match uu___378_11630 with
                   | FStar_Syntax_Syntax.Discriminator uu____11632 -> true
                   | uu____11634 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____11636,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____11648 =
                      let uu____11650 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____11650.FStar_Ident.idText  in
                    uu____11648 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___379_11657  ->
                      match uu___379_11657 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____11660 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11663) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___380_11677  ->
                   match uu___380_11677 with
                   | FStar_Syntax_Syntax.Projector uu____11679 -> true
                   | uu____11685 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____11689 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____11689 with
            | FStar_Pervasives_Native.Some uu____11696 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___397_11698 = se  in
                  let uu____11699 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____11699;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___397_11698.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___397_11698.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___397_11698.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11702) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11717) ->
           let uu____11726 = encode_sigelts env ses  in
           (match uu____11726 with
            | (g,env1) ->
                let uu____11743 =
                  FStar_All.pipe_right g
                    (FStar_List.partition
                       (fun uu___381_11766  ->
                          match uu___381_11766 with
                          | FStar_SMTEncoding_Term.Assume
                              {
                                FStar_SMTEncoding_Term.assumption_term =
                                  uu____11768;
                                FStar_SMTEncoding_Term.assumption_caption =
                                  FStar_Pervasives_Native.Some
                                  "inversion axiom";
                                FStar_SMTEncoding_Term.assumption_name =
                                  uu____11769;
                                FStar_SMTEncoding_Term.assumption_fact_ids =
                                  uu____11770;_}
                              -> false
                          | uu____11777 -> true))
                   in
                (match uu____11743 with
                 | (g',inversions) ->
                     let uu____11793 =
                       FStar_All.pipe_right g'
                         (FStar_List.partition
                            (fun uu___382_11814  ->
                               match uu___382_11814 with
                               | FStar_SMTEncoding_Term.DeclFun uu____11816
                                   -> true
                               | uu____11829 -> false))
                        in
                     (match uu____11793 with
                      | (decls,rest) ->
                          ((FStar_List.append decls
                              (FStar_List.append rest inversions)), env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,uu____11846,tps,k,uu____11849,datas) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let is_logical =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___383_11868  ->
                     match uu___383_11868 with
                     | FStar_Syntax_Syntax.Logic  -> true
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____11872 -> false))
              in
           let constructor_or_logic_type_decl c =
             if is_logical
             then
               let uu____11885 = c  in
               match uu____11885 with
               | (name,args,uu____11890,uu____11891,uu____11892) ->
                   let uu____11903 =
                     let uu____11904 =
                       let uu____11916 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____11943  ->
                                 match uu____11943 with
                                 | (uu____11952,sort,uu____11954) -> sort))
                          in
                       (name, uu____11916, FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                        in
                     FStar_SMTEncoding_Term.DeclFun uu____11904  in
                   [uu____11903]
             else
               (let uu____11965 = FStar_Ident.range_of_lid t  in
                FStar_SMTEncoding_Term.constructor_to_decl uu____11965 c)
              in
           let inversion_axioms tapp vars =
             let uu____11983 =
               FStar_All.pipe_right datas
                 (FStar_Util.for_some
                    (fun l  ->
                       let uu____11991 =
                         FStar_TypeChecker_Env.try_lookup_lid
                           env.FStar_SMTEncoding_Env.tcenv l
                          in
                       FStar_All.pipe_right uu____11991 FStar_Option.isNone))
                in
             if uu____11983
             then []
             else
               (let uu____12026 =
                  FStar_SMTEncoding_Env.fresh_fvar "x"
                    FStar_SMTEncoding_Term.Term_sort
                   in
                match uu____12026 with
                | (xxsym,xx) ->
                    let uu____12039 =
                      FStar_All.pipe_right datas
                        (FStar_List.fold_left
                           (fun uu____12078  ->
                              fun l  ->
                                match uu____12078 with
                                | (out,decls) ->
                                    let uu____12098 =
                                      FStar_TypeChecker_Env.lookup_datacon
                                        env.FStar_SMTEncoding_Env.tcenv l
                                       in
                                    (match uu____12098 with
                                     | (uu____12109,data_t) ->
                                         let uu____12111 =
                                           FStar_Syntax_Util.arrow_formals
                                             data_t
                                            in
                                         (match uu____12111 with
                                          | (args,res) ->
                                              let indices =
                                                let uu____12155 =
                                                  let uu____12156 =
                                                    FStar_Syntax_Subst.compress
                                                      res
                                                     in
                                                  uu____12156.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____12155 with
                                                | FStar_Syntax_Syntax.Tm_app
                                                    (uu____12159,indices) ->
                                                    indices
                                                | uu____12185 -> []  in
                                              let env1 =
                                                FStar_All.pipe_right args
                                                  (FStar_List.fold_left
                                                     (fun env1  ->
                                                        fun uu____12215  ->
                                                          match uu____12215
                                                          with
                                                          | (x,uu____12223)
                                                              ->
                                                              let uu____12228
                                                                =
                                                                let uu____12229
                                                                  =
                                                                  let uu____12237
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                  (uu____12237,
                                                                    [xx])
                                                                   in
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  uu____12229
                                                                 in
                                                              FStar_SMTEncoding_Env.push_term_var
                                                                env1 x
                                                                uu____12228)
                                                     env)
                                                 in
                                              let uu____12242 =
                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                  indices env1
                                                 in
                                              (match uu____12242 with
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
                                                       let uu____12267 =
                                                         FStar_List.map2
                                                           (fun v1  ->
                                                              fun a  ->
                                                                let uu____12275
                                                                  =
                                                                  let uu____12280
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                  (uu____12280,
                                                                    a)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____12275)
                                                           vars indices1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____12267
                                                         FStar_SMTEncoding_Util.mk_and_l
                                                        in
                                                     let uu____12283 =
                                                       let uu____12284 =
                                                         let uu____12289 =
                                                           let uu____12290 =
                                                             let uu____12295
                                                               =
                                                               FStar_SMTEncoding_Env.mk_data_tester
                                                                 env1 l xx
                                                                in
                                                             (uu____12295,
                                                               eqs)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____12290
                                                            in
                                                         (out, uu____12289)
                                                          in
                                                       FStar_SMTEncoding_Util.mkOr
                                                         uu____12284
                                                        in
                                                     (uu____12283,
                                                       (FStar_List.append
                                                          decls decls'))))))))
                           (FStar_SMTEncoding_Util.mkFalse, []))
                       in
                    (match uu____12039 with
                     | (data_ax,decls) ->
                         let uu____12308 =
                           FStar_SMTEncoding_Env.fresh_fvar "f"
                             FStar_SMTEncoding_Term.Fuel_sort
                            in
                         (match uu____12308 with
                          | (ffsym,ff) ->
                              let fuel_guarded_inversion =
                                let xx_has_type_sfuel =
                                  if
                                    (FStar_List.length datas) >
                                      (Prims.parse_int "1")
                                  then
                                    let uu____12325 =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [ff])
                                       in
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel
                                      uu____12325 xx tapp
                                  else
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                      xx tapp
                                   in
                                let uu____12332 =
                                  let uu____12340 =
                                    let uu____12341 =
                                      FStar_Ident.range_of_lid t  in
                                    let uu____12342 =
                                      let uu____12353 =
                                        let uu____12354 =
                                          FStar_SMTEncoding_Term.mk_fv
                                            (ffsym,
                                              FStar_SMTEncoding_Term.Fuel_sort)
                                           in
                                        let uu____12356 =
                                          let uu____12359 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          uu____12359 :: vars  in
                                        FStar_SMTEncoding_Env.add_fuel
                                          uu____12354 uu____12356
                                         in
                                      let uu____12361 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (xx_has_type_sfuel, data_ax)
                                         in
                                      ([[xx_has_type_sfuel]], uu____12353,
                                        uu____12361)
                                       in
                                    FStar_SMTEncoding_Term.mkForall
                                      uu____12341 uu____12342
                                     in
                                  let uu____12370 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                      (Prims.strcat "fuel_guarded_inversion_"
                                         t.FStar_Ident.str)
                                     in
                                  (uu____12340,
                                    (FStar_Pervasives_Native.Some
                                       "inversion axiom"), uu____12370)
                                   in
                                FStar_SMTEncoding_Util.mkAssume uu____12332
                                 in
                              FStar_List.append decls
                                [fuel_guarded_inversion])))
              in
           let uu____12376 =
             let uu____12381 =
               let uu____12382 = FStar_Syntax_Subst.compress k  in
               uu____12382.FStar_Syntax_Syntax.n  in
             match uu____12381 with
             | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                 ((FStar_List.append tps formals),
                   (FStar_Syntax_Util.comp_result kres))
             | uu____12417 -> (tps, k)  in
           (match uu____12376 with
            | (formals,res) ->
                let uu____12424 = FStar_Syntax_Subst.open_term formals res
                   in
                (match uu____12424 with
                 | (formals1,res1) ->
                     let uu____12435 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals1 env
                        in
                     (match uu____12435 with
                      | (vars,guards,env',binder_decls,uu____12460) ->
                          let arity = FStar_List.length vars  in
                          let uu____12474 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env t arity
                             in
                          (match uu____12474 with
                           | (tname,ttok,env1) ->
                               let ttok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let tapp =
                                 let uu____12504 =
                                   let uu____12512 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, uu____12512)  in
                                 FStar_SMTEncoding_Util.mkApp uu____12504  in
                               let uu____12518 =
                                 let tname_decl =
                                   let uu____12528 =
                                     let uu____12529 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun fv  ->
                                               let uu____12548 =
                                                 let uu____12550 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     fv
                                                    in
                                                 Prims.strcat tname
                                                   uu____12550
                                                  in
                                               let uu____12552 =
                                                 FStar_SMTEncoding_Term.fv_sort
                                                   fv
                                                  in
                                               (uu____12548, uu____12552,
                                                 false)))
                                        in
                                     let uu____12556 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     (tname, uu____12529,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       uu____12556, false)
                                      in
                                   constructor_or_logic_type_decl uu____12528
                                    in
                                 let uu____12564 =
                                   match vars with
                                   | [] ->
                                       let uu____12577 =
                                         let uu____12578 =
                                           let uu____12581 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tname, [])
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_3  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_3) uu____12581
                                            in
                                         FStar_SMTEncoding_Env.push_free_var
                                           env1 t arity tname uu____12578
                                          in
                                       ([], uu____12577)
                                   | uu____12593 ->
                                       let ttok_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (ttok, [],
                                             FStar_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token"))
                                          in
                                       let ttok_fresh =
                                         let uu____12603 =
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                             ()
                                            in
                                         FStar_SMTEncoding_Term.fresh_token
                                           (ttok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                           uu____12603
                                          in
                                       let ttok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars
                                          in
                                       let pats = [[ttok_app]; [tapp]]  in
                                       let name_tok_corr =
                                         let uu____12619 =
                                           let uu____12627 =
                                             let uu____12628 =
                                               FStar_Ident.range_of_lid t  in
                                             let uu____12629 =
                                               let uu____12645 =
                                                 FStar_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp)
                                                  in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 vars, uu____12645)
                                                in
                                             FStar_SMTEncoding_Term.mkForall'
                                               uu____12628 uu____12629
                                              in
                                           (uu____12627,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.strcat
                                                "token_correspondence_" ttok))
                                            in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____12619
                                          in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env1)
                                    in
                                 match uu____12564 with
                                 | (tok_decls,env2) ->
                                     let uu____12672 =
                                       FStar_Ident.lid_equals t
                                         FStar_Parser_Const.lex_t_lid
                                        in
                                     if uu____12672
                                     then (tok_decls, env2)
                                     else
                                       ((FStar_List.append tname_decl
                                           tok_decls), env2)
                                  in
                               (match uu____12518 with
                                | (decls,env2) ->
                                    let kindingAx =
                                      let uu____12700 =
                                        FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res1
                                          env' tapp
                                         in
                                      match uu____12700 with
                                      | (k1,decls1) ->
                                          let karr =
                                            if
                                              (FStar_List.length formals1) >
                                                (Prims.parse_int "0")
                                            then
                                              let uu____12722 =
                                                let uu____12723 =
                                                  let uu____12731 =
                                                    let uu____12732 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____12732
                                                     in
                                                  (uu____12731,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.strcat
                                                       "pre_kinding_" ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____12723
                                                 in
                                              [uu____12722]
                                            else []  in
                                          let uu____12740 =
                                            let uu____12743 =
                                              let uu____12746 =
                                                let uu____12747 =
                                                  let uu____12755 =
                                                    let uu____12756 =
                                                      FStar_Ident.range_of_lid
                                                        t
                                                       in
                                                    let uu____12757 =
                                                      let uu____12768 =
                                                        FStar_SMTEncoding_Util.mkImp
                                                          (guard, k1)
                                                         in
                                                      ([[tapp]], vars,
                                                        uu____12768)
                                                       in
                                                    FStar_SMTEncoding_Term.mkForall
                                                      uu____12756 uu____12757
                                                     in
                                                  (uu____12755,
                                                    FStar_Pervasives_Native.None,
                                                    (Prims.strcat "kinding_"
                                                       ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____12747
                                                 in
                                              [uu____12746]  in
                                            FStar_List.append karr
                                              uu____12743
                                             in
                                          FStar_List.append decls1
                                            uu____12740
                                       in
                                    let aux =
                                      let uu____12783 =
                                        let uu____12786 =
                                          inversion_axioms tapp vars  in
                                        let uu____12789 =
                                          let uu____12792 =
                                            let uu____12793 =
                                              FStar_Ident.range_of_lid t  in
                                            pretype_axiom uu____12793 env2
                                              tapp vars
                                             in
                                          [uu____12792]  in
                                        FStar_List.append uu____12786
                                          uu____12789
                                         in
                                      FStar_List.append kindingAx uu____12783
                                       in
                                    let g =
                                      FStar_List.append decls
                                        (FStar_List.append binder_decls aux)
                                       in
                                    (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____12798,uu____12799,uu____12800,uu____12801,uu____12802)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____12810,t,uu____12812,n_tps,uu____12814) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____12824 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____12824 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____12872 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____12872 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____12900 =
                       FStar_SMTEncoding_Env.fresh_fvar "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____12900 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____12920 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____12920 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____12999 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____12999,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____13006 =
                                   let uu____13007 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____13007, true)
                                    in
                                 let uu____13015 =
                                   let uu____13022 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____13022
                                    in
                                 FStar_All.pipe_right uu____13006 uu____13015
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
                               let uu____13034 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____13034 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____13046::uu____13047 ->
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
                                            let uu____13096 =
                                              let uu____13097 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____13097]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____13096
                                             in
                                          let uu____13123 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____13124 =
                                            let uu____13135 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____13135)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____13123 uu____13124
                                      | uu____13162 -> tok_typing  in
                                    let uu____13173 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____13173 with
                                     | (vars',guards',env'',decls_formals,uu____13198)
                                         ->
                                         let uu____13211 =
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
                                         (match uu____13211 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____13241 ->
                                                    let uu____13250 =
                                                      let uu____13251 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____13251
                                                       in
                                                    [uu____13250]
                                                 in
                                              let encode_elim uu____13267 =
                                                let uu____13268 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____13268 with
                                                | (head1,args) ->
                                                    let uu____13319 =
                                                      let uu____13320 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____13320.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____13319 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13332;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13333;_},uu____13334)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____13340 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____13340
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
                                                                  | uu____13403
                                                                    ->
                                                                    let uu____13404
                                                                    =
                                                                    let uu____13410
                                                                    =
                                                                    let uu____13412
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13412
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13410)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13404
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13435
                                                                    =
                                                                    let uu____13437
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13437
                                                                     in
                                                                    if
                                                                    uu____13435
                                                                    then
                                                                    let uu____13459
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13459]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____13462
                                                                =
                                                                let uu____13476
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____13533
                                                                     ->
                                                                    fun
                                                                    uu____13534
                                                                     ->
                                                                    match 
                                                                    (uu____13533,
                                                                    uu____13534)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13645
                                                                    =
                                                                    let uu____13653
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13653
                                                                     in
                                                                    (match uu____13645
                                                                    with
                                                                    | 
                                                                    (uu____13667,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13678
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13678
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13683
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13683
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
                                                                  uu____13476
                                                                 in
                                                              (match uu____13462
                                                               with
                                                               | (uu____13704,arg_vars,elim_eqns_or_guards,uu____13707)
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
                                                                    let uu____13734
                                                                    =
                                                                    let uu____13742
                                                                    =
                                                                    let uu____13743
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13744
                                                                    =
                                                                    let uu____13755
                                                                    =
                                                                    let uu____13756
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____13756
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13758
                                                                    =
                                                                    let uu____13759
                                                                    =
                                                                    let uu____13764
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13764)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13759
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13755,
                                                                    uu____13758)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13743
                                                                    uu____13744
                                                                     in
                                                                    (uu____13742,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13734
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13779
                                                                    =
                                                                    let uu____13780
                                                                    =
                                                                    let uu____13786
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13786,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____13780
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13779
                                                                     in
                                                                    let uu____13789
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13789
                                                                    then
                                                                    let x =
                                                                    let uu____13793
                                                                    =
                                                                    let uu____13799
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13799,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____13793
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13804
                                                                    =
                                                                    let uu____13812
                                                                    =
                                                                    let uu____13813
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13814
                                                                    =
                                                                    let uu____13825
                                                                    =
                                                                    let uu____13830
                                                                    =
                                                                    let uu____13833
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13833]
                                                                     in
                                                                    [uu____13830]
                                                                     in
                                                                    let uu____13838
                                                                    =
                                                                    let uu____13839
                                                                    =
                                                                    let uu____13844
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13846
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13844,
                                                                    uu____13846)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13839
                                                                     in
                                                                    (uu____13825,
                                                                    [x],
                                                                    uu____13838)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13813
                                                                    uu____13814
                                                                     in
                                                                    let uu____13867
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13812,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13867)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13804
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13878
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
                                                                    (let uu____13901
                                                                    =
                                                                    let uu____13902
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____13902
                                                                    dapp1  in
                                                                    [uu____13901])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13878
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____13909
                                                                    =
                                                                    let uu____13917
                                                                    =
                                                                    let uu____13918
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13919
                                                                    =
                                                                    let uu____13930
                                                                    =
                                                                    let uu____13931
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____13931
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13933
                                                                    =
                                                                    let uu____13934
                                                                    =
                                                                    let uu____13939
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____13939)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13934
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13930,
                                                                    uu____13933)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13918
                                                                    uu____13919
                                                                     in
                                                                    (uu____13917,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13909)
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
                                                         let uu____13958 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____13958
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
                                                                  | uu____14021
                                                                    ->
                                                                    let uu____14022
                                                                    =
                                                                    let uu____14028
                                                                    =
                                                                    let uu____14030
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14030
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14028)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14022
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14053
                                                                    =
                                                                    let uu____14055
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14055
                                                                     in
                                                                    if
                                                                    uu____14053
                                                                    then
                                                                    let uu____14077
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14077]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14080
                                                                =
                                                                let uu____14094
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14151
                                                                     ->
                                                                    fun
                                                                    uu____14152
                                                                     ->
                                                                    match 
                                                                    (uu____14151,
                                                                    uu____14152)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14263
                                                                    =
                                                                    let uu____14271
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14271
                                                                     in
                                                                    (match uu____14263
                                                                    with
                                                                    | 
                                                                    (uu____14285,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14296
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14296
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14301
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14301
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
                                                                  uu____14094
                                                                 in
                                                              (match uu____14080
                                                               with
                                                               | (uu____14322,arg_vars,elim_eqns_or_guards,uu____14325)
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
                                                                    let uu____14352
                                                                    =
                                                                    let uu____14360
                                                                    =
                                                                    let uu____14361
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14362
                                                                    =
                                                                    let uu____14373
                                                                    =
                                                                    let uu____14374
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14374
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14376
                                                                    =
                                                                    let uu____14377
                                                                    =
                                                                    let uu____14382
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14382)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14377
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14373,
                                                                    uu____14376)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14361
                                                                    uu____14362
                                                                     in
                                                                    (uu____14360,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14352
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14397
                                                                    =
                                                                    let uu____14398
                                                                    =
                                                                    let uu____14404
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14404,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14398
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14397
                                                                     in
                                                                    let uu____14407
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14407
                                                                    then
                                                                    let x =
                                                                    let uu____14411
                                                                    =
                                                                    let uu____14417
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14417,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14411
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14422
                                                                    =
                                                                    let uu____14430
                                                                    =
                                                                    let uu____14431
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14432
                                                                    =
                                                                    let uu____14443
                                                                    =
                                                                    let uu____14448
                                                                    =
                                                                    let uu____14451
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14451]
                                                                     in
                                                                    [uu____14448]
                                                                     in
                                                                    let uu____14456
                                                                    =
                                                                    let uu____14457
                                                                    =
                                                                    let uu____14462
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14464
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14462,
                                                                    uu____14464)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14457
                                                                     in
                                                                    (uu____14443,
                                                                    [x],
                                                                    uu____14456)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14431
                                                                    uu____14432
                                                                     in
                                                                    let uu____14485
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14430,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14485)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14422
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14496
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
                                                                    (let uu____14519
                                                                    =
                                                                    let uu____14520
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14520
                                                                    dapp1  in
                                                                    [uu____14519])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14496
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14527
                                                                    =
                                                                    let uu____14535
                                                                    =
                                                                    let uu____14536
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14537
                                                                    =
                                                                    let uu____14548
                                                                    =
                                                                    let uu____14549
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14549
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14551
                                                                    =
                                                                    let uu____14552
                                                                    =
                                                                    let uu____14557
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14557)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14552
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14548,
                                                                    uu____14551)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14536
                                                                    uu____14537
                                                                     in
                                                                    (uu____14535,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14527)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____14574 ->
                                                         ((let uu____14576 =
                                                             let uu____14582
                                                               =
                                                               let uu____14584
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____14586
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____14584
                                                                 uu____14586
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____14582)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____14576);
                                                          ([], [])))
                                                 in
                                              let uu____14594 =
                                                encode_elim ()  in
                                              (match uu____14594 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____14620 =
                                                       let uu____14623 =
                                                         let uu____14626 =
                                                           let uu____14629 =
                                                             let uu____14632
                                                               =
                                                               let uu____14633
                                                                 =
                                                                 let uu____14645
                                                                   =
                                                                   let uu____14646
                                                                    =
                                                                    let uu____14648
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14648
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____14646
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   uu____14645)
                                                                  in
                                                               FStar_SMTEncoding_Term.DeclFun
                                                                 uu____14633
                                                                in
                                                             [uu____14632]
                                                              in
                                                           let uu____14655 =
                                                             let uu____14658
                                                               =
                                                               let uu____14661
                                                                 =
                                                                 let uu____14664
                                                                   =
                                                                   let uu____14667
                                                                    =
                                                                    let uu____14670
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14675
                                                                    =
                                                                    let uu____14678
                                                                    =
                                                                    let uu____14679
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    let uu____14688
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14689
                                                                    =
                                                                    let uu____14700
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14700)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14688
                                                                    uu____14689
                                                                     in
                                                                    (uu____14687,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14679
                                                                     in
                                                                    let uu____14713
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    let uu____14717
                                                                    =
                                                                    let uu____14725
                                                                    =
                                                                    let uu____14726
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14738
                                                                    =
                                                                    let uu____14739
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14739
                                                                    vars'  in
                                                                    let uu____14741
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14738,
                                                                    uu____14741)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14726
                                                                    uu____14727
                                                                     in
                                                                    (uu____14725,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14717
                                                                     in
                                                                    [uu____14716]
                                                                     in
                                                                    uu____14678
                                                                    ::
                                                                    uu____14713
                                                                     in
                                                                    uu____14670
                                                                    ::
                                                                    uu____14675
                                                                     in
                                                                   FStar_List.append
                                                                    uu____14667
                                                                    elim
                                                                    in
                                                                 FStar_List.append
                                                                   decls_pred
                                                                   uu____14664
                                                                  in
                                                               FStar_List.append
                                                                 decls_formals
                                                                 uu____14661
                                                                in
                                                             FStar_List.append
                                                               proxy_fresh
                                                               uu____14658
                                                              in
                                                           FStar_List.append
                                                             uu____14629
                                                             uu____14655
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____14626
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____14623
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____14620
                                                      in
                                                   ((FStar_List.append
                                                       datacons g), env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14779  ->
              fun se  ->
                match uu____14779 with
                | (g,env1) ->
                    let uu____14799 = encode_sigelt env1 se  in
                    (match uu____14799 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14867 =
        match uu____14867 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____14904 ->
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
                 ((let uu____14912 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14912
                   then
                     let uu____14917 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14919 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14921 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14917 uu____14919 uu____14921
                   else ());
                  (let uu____14926 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____14926 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14944 =
                         let uu____14952 =
                           let uu____14954 =
                             let uu____14956 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____14956
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____14954  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____14952
                          in
                       (match uu____14944 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____14976 = FStar_Options.log_queries ()
                                 in
                              if uu____14976
                              then
                                let uu____14979 =
                                  let uu____14981 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14983 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14985 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14981 uu____14983 uu____14985
                                   in
                                FStar_Pervasives_Native.Some uu____14979
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15009,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15029 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15029 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15056 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15056 with | (uu____15083,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15136  ->
              match uu____15136 with
              | (l,uu____15145,uu____15146) ->
                  let uu____15149 =
                    let uu____15161 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____15161, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____15149))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15194  ->
              match uu____15194 with
              | (l,uu____15205,uu____15206) ->
                  let uu____15209 =
                    let uu____15210 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____15210
                     in
                  let uu____15213 =
                    let uu____15216 =
                      let uu____15217 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15217  in
                    [uu____15216]  in
                  uu____15209 :: uu____15213))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15246 =
      let uu____15249 =
        let uu____15250 = FStar_Util.psmap_empty ()  in
        let uu____15265 = FStar_Util.psmap_empty ()  in
        let uu____15268 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15272 =
          let uu____15274 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15274 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15250;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15265;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____15268;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15272;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____15249]  in
    FStar_ST.op_Colon_Equals last_env uu____15246
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15316 = FStar_ST.op_Bang last_env  in
      match uu____15316 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15344 ->
          let uu___398_15347 = e  in
          let uu____15348 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___398_15347.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___398_15347.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___398_15347.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___398_15347.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___398_15347.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___398_15347.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___398_15347.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___398_15347.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15348;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___398_15347.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15356 = FStar_ST.op_Bang last_env  in
    match uu____15356 with
    | [] -> failwith "Empty env stack"
    | uu____15383::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15415  ->
    let uu____15416 = FStar_ST.op_Bang last_env  in
    match uu____15416 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15476  ->
    let uu____15477 = FStar_ST.op_Bang last_env  in
    match uu____15477 with
    | [] -> failwith "Popping an empty stack"
    | uu____15504::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15541  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15594  ->
         let uu____15595 = snapshot_env ()  in
         match uu____15595 with
         | (env_depth,()) ->
             let uu____15617 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____15617 with
              | (varops_depth,()) ->
                  let uu____15639 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____15639 with
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
        (fun uu____15697  ->
           let uu____15698 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____15698 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____15793 = snapshot msg  in () 
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
        | (uu____15839::uu____15840,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___399_15848 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___399_15848.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___399_15848.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___399_15848.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15849 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____15869 =
        let uu____15872 =
          let uu____15873 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____15873  in
        let uu____15874 = open_fact_db_tags env  in uu____15872 ::
          uu____15874
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15869
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____15901 = encode_sigelt env se  in
      match uu____15901 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15946 = FStar_Options.log_queries ()  in
        if uu____15946
        then
          let uu____15951 =
            let uu____15952 =
              let uu____15954 =
                let uu____15956 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15956 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15954  in
            FStar_SMTEncoding_Term.Caption uu____15952  in
          uu____15951 :: decls
        else decls  in
      (let uu____15975 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____15975
       then
         let uu____15978 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____15978
       else ());
      (let env =
         let uu____15984 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____15984 tcenv  in
       let uu____15985 = encode_top_level_facts env se  in
       match uu____15985 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____15999 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____15999)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16013 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16013
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16028 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____16028
          then
            let uu____16031 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16031
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16077  ->
                    fun se  ->
                      match uu____16077 with
                      | (g,env2) ->
                          let uu____16097 = encode_top_level_facts env2 se
                             in
                          (match uu____16097 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16120 =
            encode_signature
              (let uu___400_16129 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___400_16129.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___400_16129.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___400_16129.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___400_16129.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___400_16129.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___400_16129.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___400_16129.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___400_16129.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___400_16129.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___400_16129.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16120 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____16149 = FStar_Options.log_queries ()  in
                if uu____16149
                then
                  let msg = Prims.strcat "Externals for " name  in
                  [FStar_SMTEncoding_Term.Module
                     (name,
                       (FStar_List.append
                          ((FStar_SMTEncoding_Term.Caption msg) :: decls1)
                          [FStar_SMTEncoding_Term.Caption
                             (Prims.strcat "End " msg)]))]
                else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
              (set_env
                 (let uu___401_16169 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___401_16169.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___401_16169.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___401_16169.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___401_16169.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___401_16169.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___401_16169.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___401_16169.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___401_16169.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___401_16169.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___401_16169.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____16172 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16172
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let decls1 = caption decls  in
                FStar_SMTEncoding_Z3.giveZ3 decls1))))
  
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
        (let uu____16237 =
           let uu____16239 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16239.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16237);
        (let env =
           let uu____16241 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16241 tcenv  in
         let uu____16242 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16281 = aux rest  in
                 (match uu____16281 with
                  | (out,rest1) ->
                      let t =
                        let uu____16309 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16309 with
                        | FStar_Pervasives_Native.Some uu____16312 ->
                            let uu____16313 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16313
                              x.FStar_Syntax_Syntax.sort
                        | uu____16314 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16318 =
                        let uu____16321 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___402_16324 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___402_16324.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___402_16324.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16321 :: out  in
                      (uu____16318, rest1))
             | uu____16329 -> ([], bindings)  in
           let uu____16336 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16336 with
           | (closing,bindings) ->
               let uu____16363 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16363, bindings)
            in
         match uu____16242 with
         | (q1,bindings) ->
             let uu____16394 = encode_env_bindings env bindings  in
             (match uu____16394 with
              | (env_decls,env1) ->
                  ((let uu____16416 =
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
                    if uu____16416
                    then
                      let uu____16423 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16423
                    else ());
                   (let uu____16428 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16428 with
                    | (phi,qdecls) ->
                        let uu____16449 =
                          let uu____16454 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16454 phi
                           in
                        (match uu____16449 with
                         | (labels,phi1) ->
                             let uu____16471 = encode_labels labels  in
                             (match uu____16471 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____16507 =
                                      FStar_Options.log_queries ()  in
                                    if uu____16507
                                    then
                                      let uu____16512 =
                                        let uu____16513 =
                                          let uu____16515 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____16515
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____16513
                                         in
                                      [uu____16512]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____16524 =
                                      let uu____16532 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16533 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____16532,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16533)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16524
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
  