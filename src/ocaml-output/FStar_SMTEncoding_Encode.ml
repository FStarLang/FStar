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
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
              let uu____5321 =
                ((let uu____5325 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5325) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5321
              then
                let arg_sorts =
                  let uu____5339 =
                    let uu____5340 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5340.FStar_Syntax_Syntax.n  in
                  match uu____5339 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5346) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5384  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5391 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5393 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5393 with
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
                (let uu____5435 = prims.is lid  in
                 if uu____5435
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5446 = prims.mk lid vname  in
                   match uu____5446 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5480 =
                      let uu____5499 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5499 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5527 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5527
                            then
                              let uu____5532 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___383_5535 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___383_5535.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___383_5535.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___383_5535.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___383_5535.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___383_5535.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___383_5535.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___383_5535.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___383_5535.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___383_5535.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___383_5535.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___383_5535.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___383_5535.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___383_5535.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___383_5535.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___383_5535.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___383_5535.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___383_5535.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___383_5535.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___383_5535.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___383_5535.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___383_5535.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___383_5535.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___383_5535.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___383_5535.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___383_5535.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___383_5535.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___383_5535.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___383_5535.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___383_5535.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___383_5535.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___383_5535.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___383_5535.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___383_5535.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___383_5535.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___383_5535.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___383_5535.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___383_5535.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___383_5535.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___383_5535.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___383_5535.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___383_5535.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___383_5535.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5532
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5558 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5558)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5480 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___373_5666  ->
                                  match uu___373_5666 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____5670 = FStar_Util.prefix vars
                                         in
                                      (match uu____5670 with
                                       | (uu____5703,xxv) ->
                                           let xx =
                                             let uu____5742 =
                                               let uu____5743 =
                                                 let uu____5749 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____5749,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____5743
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____5742
                                              in
                                           let uu____5752 =
                                             let uu____5753 =
                                               let uu____5761 =
                                                 let uu____5762 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5763 =
                                                   let uu____5774 =
                                                     let uu____5775 =
                                                       let uu____5780 =
                                                         let uu____5781 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____5781
                                                          in
                                                       (vapp, uu____5780)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____5775
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5774)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5762 uu____5763
                                                  in
                                               (uu____5761,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.strcat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5753
                                              in
                                           [uu____5752])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____5796 = FStar_Util.prefix vars
                                         in
                                      (match uu____5796 with
                                       | (uu____5829,xxv) ->
                                           let xx =
                                             let uu____5868 =
                                               let uu____5869 =
                                                 let uu____5875 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____5875,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____5869
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____5868
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
                                           let uu____5886 =
                                             let uu____5887 =
                                               let uu____5895 =
                                                 let uu____5896 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5897 =
                                                   let uu____5908 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5908)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5896 uu____5897
                                                  in
                                               (uu____5895,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.strcat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5887
                                              in
                                           [uu____5886])
                                  | uu____5921 -> []))
                           in
                        let uu____5922 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____5922 with
                         | (vars,guards,env',decls1,uu____5949) ->
                             let uu____5962 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____5975 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____5975, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____5979 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____5979 with
                                    | (g,ds) ->
                                        let uu____5992 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____5992,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____5962 with
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
                                  let should_thunk =
                                    let is_type1 t =
                                      let uu____6020 =
                                        let uu____6021 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6021.FStar_Syntax_Syntax.n  in
                                      match uu____6020 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____6025 -> true
                                      | uu____6027 -> false  in
                                    let is_squash1 t =
                                      let uu____6036 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____6036 with
                                      | (head1,uu____6055) ->
                                          let uu____6080 =
                                            let uu____6081 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____6081.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6080 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____6086;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____6087;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____6089;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____6090;_};_},uu____6091)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____6099 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____6104 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____6104))
                                       &&
                                       (let uu____6110 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____6110))
                                      &&
                                      (let uu____6113 = is_type1 t_norm  in
                                       Prims.op_Negation uu____6113)
                                     in
                                  let uu____6115 =
                                    match vars with
                                    | [] when should_thunk ->
                                        (true, [dummy_var])
                                    | uu____6174 -> (false, vars)  in
                                  (match uu____6115 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____6226 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____6226 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____6264 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____6273 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____6273
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____6284 ->
                                                  let uu____6293 =
                                                    let uu____6301 =
                                                      get_vtok ()  in
                                                    (uu____6301, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6293
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____6308 =
                                                let uu____6316 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____6316)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____6308
                                               in
                                            let uu____6330 =
                                              let vname_decl =
                                                let uu____6338 =
                                                  let uu____6350 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____6350,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____6338
                                                 in
                                              let uu____6361 =
                                                let env2 =
                                                  let uu___384_6367 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.cache
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.cache);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___384_6367.FStar_SMTEncoding_Env.encoding_quantifier)
                                                  }  in
                                                let uu____6368 =
                                                  let uu____6370 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____6370
                                                   in
                                                if uu____6368
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____6361 with
                                              | (tok_typing,decls2) ->
                                                  let uu____6387 =
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
                                                        let uu____6413 =
                                                          let uu____6414 =
                                                            let uu____6417 =
                                                              let uu____6418
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____6418
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____6417
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____6414
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [tok_typing1]),
                                                          uu____6413)
                                                    | uu____6428 when thunked
                                                        ->
                                                        let uu____6439 =
                                                          false &&
                                                            (FStar_Options.protect_top_level_axioms
                                                               ())
                                                           in
                                                        if uu____6439
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____6455
                                                                 =
                                                                 let uu____6463
                                                                   =
                                                                   let uu____6466
                                                                    =
                                                                    let uu____6469
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____6469]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____6466
                                                                    in
                                                                 ("FStar.Pervasives.intro_ambient",
                                                                   uu____6463)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____6455
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____6477 =
                                                               let uu____6485
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____6485,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.strcat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____6477
                                                              in
                                                           ((FStar_List.append
                                                               decls2
                                                               [intro_ambient1]),
                                                             env1))
                                                    | uu____6492 ->
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
                                                          let uu____6516 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____6517 =
                                                            let uu____6528 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____6528)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____6516
                                                            uu____6517
                                                           in
                                                        let name_tok_corr =
                                                          let uu____6538 =
                                                            let uu____6546 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____6546,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____6538
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
                                                            let uu____6557 =
                                                              let uu____6558
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____6558]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____6557
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____6585 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6586 =
                                                              let uu____6597
                                                                =
                                                                let uu____6598
                                                                  =
                                                                  let uu____6603
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____6604
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____6603,
                                                                    uu____6604)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____6598
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____6597)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6585
                                                              uu____6586
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
                                                  (match uu____6387 with
                                                   | (tok_decl,env2) ->
                                                       ((vname_decl ::
                                                         tok_decl), env2))
                                               in
                                            (match uu____6330 with
                                             | (decls2,env2) ->
                                                 let uu____6661 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____6671 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____6671 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____6686 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____6686, decls)
                                                    in
                                                 (match uu____6661 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____6703 =
                                                          let uu____6711 =
                                                            let uu____6712 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6713 =
                                                              let uu____6724
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____6724)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6712
                                                              uu____6713
                                                             in
                                                          (uu____6711,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6703
                                                         in
                                                      let freshness =
                                                        let uu____6740 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____6740
                                                        then
                                                          let uu____6748 =
                                                            let uu____6749 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6750 =
                                                              let uu____6763
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____6770
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____6763,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____6770)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____6749
                                                              uu____6750
                                                             in
                                                          let uu____6776 =
                                                            let uu____6779 =
                                                              let uu____6780
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____6780
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____6779]  in
                                                          uu____6748 ::
                                                            uu____6776
                                                        else []  in
                                                      let g =
                                                        let uu____6786 =
                                                          let uu____6789 =
                                                            let uu____6792 =
                                                              let uu____6795
                                                                =
                                                                let uu____6798
                                                                  =
                                                                  mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1
                                                                   in
                                                                typingAx ::
                                                                  uu____6798
                                                                 in
                                                              FStar_List.append
                                                                freshness
                                                                uu____6795
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____6792
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6789
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____6786
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl
            Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____6840 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6840 with
          | FStar_Pervasives_Native.None  ->
              let uu____6851 = encode_free_var false env x t t_norm []  in
              (match uu____6851 with
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
            let uu____6922 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6922 with
            | (decls,env1) ->
                let uu____6941 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6941
                then
                  let uu____6950 =
                    let uu____6953 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6953  in
                  (uu____6950, env1)
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
             (fun uu____7013  ->
                fun lb  ->
                  match uu____7013 with
                  | (decls,env1) ->
                      let uu____7033 =
                        let uu____7040 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7040
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7033 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7073 = FStar_Syntax_Util.head_and_args t  in
    match uu____7073 with
    | (hd1,args) ->
        let uu____7117 =
          let uu____7118 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7118.FStar_Syntax_Syntax.n  in
        (match uu____7117 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7124,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7148 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7159 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___385_7167 = en  in
    let uu____7168 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___385_7167.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___385_7167.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___385_7167.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___385_7167.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___385_7167.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7168;
      FStar_SMTEncoding_Env.nolabels =
        (uu___385_7167.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___385_7167.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___385_7167.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___385_7167.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___385_7167.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7200  ->
      fun quals  ->
        match uu____7200 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7307 = FStar_Util.first_N nbinders formals  in
              match uu____7307 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7408  ->
                         fun uu____7409  ->
                           match (uu____7408, uu____7409) with
                           | ((formal,uu____7435),(binder,uu____7437)) ->
                               let uu____7458 =
                                 let uu____7465 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7465)  in
                               FStar_Syntax_Syntax.NT uu____7458) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7479 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7520  ->
                              match uu____7520 with
                              | (x,i) ->
                                  let uu____7539 =
                                    let uu___386_7540 = x  in
                                    let uu____7541 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_7540.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_7540.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7541
                                    }  in
                                  (uu____7539, i)))
                       in
                    FStar_All.pipe_right uu____7479
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7565 =
                      let uu____7570 = FStar_Syntax_Subst.compress body  in
                      let uu____7571 =
                        let uu____7572 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7572
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7570 uu____7571
                       in
                    uu____7565 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___387_7623 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___387_7623.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___387_7623.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___387_7623.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___387_7623.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___387_7623.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___387_7623.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___387_7623.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___387_7623.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___387_7623.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___387_7623.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___387_7623.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___387_7623.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___387_7623.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___387_7623.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___387_7623.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___387_7623.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___387_7623.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___387_7623.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___387_7623.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___387_7623.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___387_7623.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___387_7623.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___387_7623.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___387_7623.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___387_7623.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___387_7623.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___387_7623.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___387_7623.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___387_7623.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___387_7623.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___387_7623.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___387_7623.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___387_7623.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___387_7623.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___387_7623.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___387_7623.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___387_7623.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___387_7623.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___387_7623.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___387_7623.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___387_7623.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___387_7623.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7695  ->
                       fun uu____7696  ->
                         match (uu____7695, uu____7696) with
                         | ((x,uu____7722),(b,uu____7724)) ->
                             let uu____7745 =
                               let uu____7752 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7752)  in
                             FStar_Syntax_Syntax.NT uu____7745) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7777 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7777
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7806 ->
                    let uu____7813 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7813
                | uu____7814 when Prims.op_Negation norm1 ->
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
                | uu____7817 ->
                    let uu____7818 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7818)
                 in
              let aux t1 e1 =
                let uu____7860 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7860 with
                | (binders,body,lopt) ->
                    let uu____7892 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7908 -> arrow_formals_comp_norm false t1  in
                    (match uu____7892 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7942 =
                           if nformals < nbinders
                           then
                             let uu____7986 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7986 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____8070 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____8070)
                           else
                             if nformals > nbinders
                             then
                               (let uu____8110 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____8110 with
                                | (binders1,body1) ->
                                    let uu____8163 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____8163))
                             else
                               (let uu____8176 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____8176))
                            in
                         (match uu____7942 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____8236 = aux t e  in
              match uu____8236 with
              | (binders,body,comp) ->
                  let uu____8282 =
                    let uu____8293 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____8293
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____8308 = aux comp1 body1  in
                      match uu____8308 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____8282 with
                   | (binders1,body1,comp1) ->
                       let uu____8391 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____8391, comp1))
               in
            (try
               (fun uu___389_8418  ->
                  match () with
                  | () ->
                      let uu____8425 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8425
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8441 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8504  ->
                                   fun lb  ->
                                     match uu____8504 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8559 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8559
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8565 =
                                             let uu____8574 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8574
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8565 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8441 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____8715;
                                    FStar_Syntax_Syntax.lbeff = uu____8716;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8718;
                                    FStar_Syntax_Syntax.lbpos = uu____8719;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8743 =
                                     let uu____8750 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8750 with
                                     | (tcenv',uu____8766,e_t) ->
                                         let uu____8772 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8783 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8772 with
                                          | (e1,t_norm1) ->
                                              ((let uu___390_8800 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___390_8800.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8743 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8810 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____8810 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8830 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8830
                                               then
                                                 let uu____8835 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8838 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8835 uu____8838
                                               else ());
                                              (let uu____8843 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8843 with
                                               | (vars,_guards,env'1,binder_decls,uu____8870)
                                                   ->
                                                   let uu____8883 =
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
                                                         let uu____8900 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____8900
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____8922 =
                                                          let uu____8923 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____8924 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____8923 fvb
                                                            uu____8924
                                                           in
                                                        (vars, uu____8922))
                                                      in
                                                   (match uu____8883 with
                                                    | (vars1,app) ->
                                                        let uu____8935 =
                                                          let is_logical =
                                                            let uu____8948 =
                                                              let uu____8949
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____8949.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____8948
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____8955 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____8959 =
                                                              let uu____8960
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8960
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____8959
                                                              (fun lid  ->
                                                                 let uu____8969
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____8969
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____8970 =
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
                                                          if uu____8970
                                                          then
                                                            let uu____8986 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____8987 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app, uu____8986,
                                                              uu____8987)
                                                          else
                                                            (let uu____8998 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____8998))
                                                           in
                                                        (match uu____8935
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____9022
                                                                 =
                                                                 let uu____9030
                                                                   =
                                                                   let uu____9031
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____9032
                                                                    =
                                                                    let uu____9043
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____9043)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____9031
                                                                    uu____9032
                                                                    in
                                                                 let uu____9052
                                                                   =
                                                                   let uu____9053
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9053
                                                                    in
                                                                 (uu____9030,
                                                                   uu____9052,
                                                                   (Prims.strcat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____9022
                                                                in
                                                             let uu____9059 =
                                                               let uu____9062
                                                                 =
                                                                 let uu____9065
                                                                   =
                                                                   let uu____9068
                                                                    =
                                                                    let uu____9071
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    FStar_List.append
                                                                    [eqn]
                                                                    uu____9071
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____9068
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____9065
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____9062
                                                                in
                                                             (uu____9059,
                                                               env2)))))))
                               | uu____9076 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9136 =
                                   let uu____9142 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       "fuel"
                                      in
                                   (uu____9142,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____9136  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9148 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9201  ->
                                         fun fvb  ->
                                           match uu____9201 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9256 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9256
                                                  in
                                               let gtok =
                                                 let uu____9260 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9260
                                                  in
                                               let env4 =
                                                 let uu____9263 =
                                                   let uu____9266 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9266
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9263
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9148 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9393
                                     t_norm uu____9395 =
                                     match (uu____9393, uu____9395) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9427;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9428;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9430;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9431;_})
                                         ->
                                         let uu____9458 =
                                           let uu____9465 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9465 with
                                           | (tcenv',uu____9481,e_t) ->
                                               let uu____9487 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9498 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9487 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___391_9515 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___391_9515.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9458 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9530 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9530
                                                then
                                                  let uu____9535 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9537 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9539 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9535 uu____9537
                                                    uu____9539
                                                else ());
                                               (let uu____9544 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____9544 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9573 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9573 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9597 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9597
                                                           then
                                                             let uu____9602 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9604 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9607 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9609 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9602
                                                               uu____9604
                                                               uu____9607
                                                               uu____9609
                                                           else ());
                                                          (let uu____9614 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9614
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9645)
                                                               ->
                                                               let uu____9658
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9671
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9671,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9675
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9675
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9688
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9688,
                                                                    decls0))
                                                                  in
                                                               (match uu____9658
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
                                                                    let uu____9711
                                                                    =
                                                                    let uu____9723
                                                                    =
                                                                    let uu____9726
                                                                    =
                                                                    let uu____9729
                                                                    =
                                                                    let uu____9732
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9732
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____9729
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9726
                                                                     in
                                                                    (g,
                                                                    uu____9723,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9711
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
                                                                    let uu____9762
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9762
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
                                                                    let uu____9777
                                                                    =
                                                                    let uu____9780
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9780
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9777
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9786
                                                                    =
                                                                    let uu____9789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9789
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9786
                                                                     in
                                                                    let uu____9794
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9794
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9812
                                                                    =
                                                                    let uu____9820
                                                                    =
                                                                    let uu____9821
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9822
                                                                    =
                                                                    let uu____9838
                                                                    =
                                                                    let uu____9839
                                                                    =
                                                                    let uu____9844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9844)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9839
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9838)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9821
                                                                    uu____9822
                                                                     in
                                                                    let uu____9858
                                                                    =
                                                                    let uu____9859
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9859
                                                                     in
                                                                    (uu____9820,
                                                                    uu____9858,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9812
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9866
                                                                    =
                                                                    let uu____9874
                                                                    =
                                                                    let uu____9875
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9876
                                                                    =
                                                                    let uu____9887
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9887)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9875
                                                                    uu____9876
                                                                     in
                                                                    (uu____9874,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9866
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9901
                                                                    =
                                                                    let uu____9909
                                                                    =
                                                                    let uu____9910
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9911
                                                                    =
                                                                    let uu____9922
                                                                    =
                                                                    let uu____9923
                                                                    =
                                                                    let uu____9928
                                                                    =
                                                                    let uu____9929
                                                                    =
                                                                    let uu____9932
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9932
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9929
                                                                     in
                                                                    (gsapp,
                                                                    uu____9928)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9923
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9922)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9910
                                                                    uu____9911
                                                                     in
                                                                    (uu____9909,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9901
                                                                     in
                                                                    let uu____9946
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
                                                                    let uu____9958
                                                                    =
                                                                    let uu____9959
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____9959
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9958
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9961
                                                                    =
                                                                    let uu____9969
                                                                    =
                                                                    let uu____9970
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9971
                                                                    =
                                                                    let uu____9982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9982)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9970
                                                                    uu____9971
                                                                     in
                                                                    (uu____9969,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9961
                                                                     in
                                                                    let uu____9995
                                                                    =
                                                                    let uu____10004
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____10004
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10019
                                                                    =
                                                                    let uu____10022
                                                                    =
                                                                    let uu____10023
                                                                    =
                                                                    let uu____10031
                                                                    =
                                                                    let uu____10032
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10033
                                                                    =
                                                                    let uu____10044
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10044)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10032
                                                                    uu____10033
                                                                     in
                                                                    (uu____10031,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10023
                                                                     in
                                                                    [uu____10022]
                                                                     in
                                                                    (d3,
                                                                    uu____10019)
                                                                     in
                                                                    match uu____9995
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9946
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
                                   let uu____10107 =
                                     let uu____10120 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10183  ->
                                          fun uu____10184  ->
                                            match (uu____10183, uu____10184)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10309 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10309 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10120
                                      in
                                   (match uu____10107 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10382 =
                                          let isDeclFun uu___374_10397 =
                                            match uu___374_10397 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10399 -> true
                                            | uu____10412 -> false  in
                                          let uu____10414 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10414
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____10382 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10454 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___375_10460  ->
                                        match uu___375_10460 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10463 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10471 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10471)))
                                in
                             if uu____10454
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___393_10493  ->
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
                   let uu____10531 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10531
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
        let uu____10601 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10601 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10607 = encode_sigelt' env se  in
      match uu____10607 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10619 =
                  let uu____10620 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____10620  in
                [uu____10619]
            | uu____10623 ->
                let uu____10624 =
                  let uu____10627 =
                    let uu____10628 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10628  in
                  uu____10627 :: g  in
                let uu____10631 =
                  let uu____10634 =
                    let uu____10635 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10635  in
                  [uu____10634]  in
                FStar_List.append uu____10624 uu____10631
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____10645 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____10645
       then
         let uu____10650 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____10650
       else ());
      (let is_opaque_to_smt t =
         let uu____10662 =
           let uu____10663 = FStar_Syntax_Subst.compress t  in
           uu____10663.FStar_Syntax_Syntax.n  in
         match uu____10662 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10668)) -> s = "opaque_to_smt"
         | uu____10673 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____10682 =
           let uu____10683 = FStar_Syntax_Subst.compress t  in
           uu____10683.FStar_Syntax_Syntax.n  in
         match uu____10682 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10688)) -> s = "uninterpreted_by_smt"
         | uu____10693 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10699 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____10705 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____10717 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____10718 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10719 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____10732 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____10734 =
             let uu____10736 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____10736  in
           if uu____10734
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____10765 ->
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
                let uu____10797 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____10797 with
                | (formals,uu____10817) ->
                    let arity = FStar_List.length formals  in
                    let uu____10841 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____10841 with
                     | (aname,atok,env2) ->
                         let uu____10867 =
                           let uu____10872 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____10872 env2
                            in
                         (match uu____10867 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____10884 =
                                  let uu____10885 =
                                    let uu____10897 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____10917  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____10897,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____10885
                                   in
                                [uu____10884;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____10934 =
                                let aux uu____10980 uu____10981 =
                                  match (uu____10980, uu____10981) with
                                  | ((bv,uu____11025),(env3,acc_sorts,acc))
                                      ->
                                      let uu____11057 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____11057 with
                                       | (xxsym,xx,env4) ->
                                           let uu____11080 =
                                             let uu____11083 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____11083 :: acc_sorts  in
                                           (env4, uu____11080, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____10934 with
                               | (uu____11115,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____11131 =
                                       let uu____11139 =
                                         let uu____11140 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11141 =
                                           let uu____11152 =
                                             let uu____11153 =
                                               let uu____11158 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____11158)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____11153
                                              in
                                           ([[app]], xs_sorts, uu____11152)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11140 uu____11141
                                          in
                                       (uu____11139,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.strcat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11131
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____11173 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____11173
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____11176 =
                                       let uu____11184 =
                                         let uu____11185 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11186 =
                                           let uu____11197 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____11197)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11185 uu____11186
                                          in
                                       (uu____11184,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.strcat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11176
                                      in
                                   (env2,
                                     (FStar_List.append decls
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence]))))))
                 in
              let uu____11212 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____11212 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11238,uu____11239)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____11240 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____11240 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11262,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____11269 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___376_11275  ->
                       match uu___376_11275 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____11278 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11284 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____11287 -> false))
                in
             Prims.op_Negation uu____11269  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____11297 =
                let uu____11304 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____11304 env fv t quals  in
              match uu____11297 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____11322 =
                      FStar_SMTEncoding_Term.mk_fv
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____11322
                     in
                  let uu____11324 =
                    let uu____11325 =
                      primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                        lid tname tsym
                       in
                    FStar_List.append decls uu____11325  in
                  (uu____11324, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____11331 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____11331 with
            | (uvs,f1) ->
                let env1 =
                  let uu___394_11343 = env  in
                  let uu____11344 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___394_11343.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___394_11343.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___394_11343.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____11344;
                    FStar_SMTEncoding_Env.warn =
                      (uu___394_11343.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.cache =
                      (uu___394_11343.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___394_11343.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___394_11343.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___394_11343.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___394_11343.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___394_11343.FStar_SMTEncoding_Env.encoding_quantifier)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____11346 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____11346 with
                 | (f3,decls) ->
                     let g =
                       let uu____11360 =
                         let uu____11361 =
                           let uu____11369 =
                             let uu____11370 =
                               let uu____11372 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.format1 "Assumption: %s"
                                 uu____11372
                                in
                             FStar_Pervasives_Native.Some uu____11370  in
                           let uu____11376 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                               (Prims.strcat "assumption_" l.FStar_Ident.str)
                              in
                           (f3, uu____11369, uu____11376)  in
                         FStar_SMTEncoding_Util.mkAssume uu____11361  in
                       [uu____11360]  in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____11381) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____11395 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____11417 =
                        let uu____11420 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____11420.FStar_Syntax_Syntax.fv_name  in
                      uu____11417.FStar_Syntax_Syntax.v  in
                    let uu____11421 =
                      let uu____11423 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____11423  in
                    if uu____11421
                    then
                      let val_decl =
                        let uu___395_11455 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___395_11455.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___395_11455.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___395_11455.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____11456 = encode_sigelt' env1 val_decl  in
                      match uu____11456 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____11395 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____11492,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____11494;
                           FStar_Syntax_Syntax.lbtyp = uu____11495;
                           FStar_Syntax_Syntax.lbeff = uu____11496;
                           FStar_Syntax_Syntax.lbdef = uu____11497;
                           FStar_Syntax_Syntax.lbattrs = uu____11498;
                           FStar_Syntax_Syntax.lbpos = uu____11499;_}::[]),uu____11500)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____11519 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____11519 with
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
                  let uu____11557 =
                    let uu____11560 =
                      let uu____11561 =
                        let uu____11569 =
                          let uu____11570 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____11571 =
                            let uu____11582 =
                              let uu____11583 =
                                let uu____11588 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____11588)  in
                              FStar_SMTEncoding_Util.mkEq uu____11583  in
                            ([[b2t_x]], [xx], uu____11582)  in
                          FStar_SMTEncoding_Term.mkForall uu____11570
                            uu____11571
                           in
                        (uu____11569,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____11561  in
                    [uu____11560]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____11557
                   in
                (decls, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____11626,uu____11627) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___377_11637  ->
                   match uu___377_11637 with
                   | FStar_Syntax_Syntax.Discriminator uu____11639 -> true
                   | uu____11641 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____11643,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____11655 =
                      let uu____11657 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____11657.FStar_Ident.idText  in
                    uu____11655 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___378_11664  ->
                      match uu___378_11664 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____11667 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11670) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_11684  ->
                   match uu___379_11684 with
                   | FStar_Syntax_Syntax.Projector uu____11686 -> true
                   | uu____11692 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____11696 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____11696 with
            | FStar_Pervasives_Native.Some uu____11703 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___396_11705 = se  in
                  let uu____11706 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____11706;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___396_11705.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___396_11705.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___396_11705.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11709) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11724) ->
           let uu____11733 = encode_sigelts env ses  in
           (match uu____11733 with
            | (g,env1) ->
                let uu____11750 =
                  FStar_All.pipe_right g
                    (FStar_List.partition
                       (fun uu___380_11773  ->
                          match uu___380_11773 with
                          | FStar_SMTEncoding_Term.Assume
                              {
                                FStar_SMTEncoding_Term.assumption_term =
                                  uu____11775;
                                FStar_SMTEncoding_Term.assumption_caption =
                                  FStar_Pervasives_Native.Some
                                  "inversion axiom";
                                FStar_SMTEncoding_Term.assumption_name =
                                  uu____11776;
                                FStar_SMTEncoding_Term.assumption_fact_ids =
                                  uu____11777;_}
                              -> false
                          | uu____11784 -> true))
                   in
                (match uu____11750 with
                 | (g',inversions) ->
                     let uu____11800 =
                       FStar_All.pipe_right g'
                         (FStar_List.partition
                            (fun uu___381_11821  ->
                               match uu___381_11821 with
                               | FStar_SMTEncoding_Term.DeclFun uu____11823
                                   -> true
                               | uu____11836 -> false))
                        in
                     (match uu____11800 with
                      | (decls,rest) ->
                          ((FStar_List.append decls
                              (FStar_List.append rest inversions)), env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,uu____11853,tps,k,uu____11856,datas) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let is_logical =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___382_11875  ->
                     match uu___382_11875 with
                     | FStar_Syntax_Syntax.Logic  -> true
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____11879 -> false))
              in
           let constructor_or_logic_type_decl c =
             if is_logical
             then
               let uu____11892 = c  in
               match uu____11892 with
               | (name,args,uu____11897,uu____11898,uu____11899) ->
                   let uu____11910 =
                     let uu____11911 =
                       let uu____11923 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____11950  ->
                                 match uu____11950 with
                                 | (uu____11959,sort,uu____11961) -> sort))
                          in
                       (name, uu____11923, FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                        in
                     FStar_SMTEncoding_Term.DeclFun uu____11911  in
                   [uu____11910]
             else
               (let uu____11972 = FStar_Ident.range_of_lid t  in
                FStar_SMTEncoding_Term.constructor_to_decl uu____11972 c)
              in
           let inversion_axioms tapp vars =
             let uu____11990 =
               FStar_All.pipe_right datas
                 (FStar_Util.for_some
                    (fun l  ->
                       let uu____11998 =
                         FStar_TypeChecker_Env.try_lookup_lid
                           env.FStar_SMTEncoding_Env.tcenv l
                          in
                       FStar_All.pipe_right uu____11998 FStar_Option.isNone))
                in
             if uu____11990
             then []
             else
               (let uu____12033 =
                  FStar_SMTEncoding_Env.fresh_fvar "x"
                    FStar_SMTEncoding_Term.Term_sort
                   in
                match uu____12033 with
                | (xxsym,xx) ->
                    let uu____12046 =
                      FStar_All.pipe_right datas
                        (FStar_List.fold_left
                           (fun uu____12085  ->
                              fun l  ->
                                match uu____12085 with
                                | (out,decls) ->
                                    let uu____12105 =
                                      FStar_TypeChecker_Env.lookup_datacon
                                        env.FStar_SMTEncoding_Env.tcenv l
                                       in
                                    (match uu____12105 with
                                     | (uu____12116,data_t) ->
                                         let uu____12118 =
                                           FStar_Syntax_Util.arrow_formals
                                             data_t
                                            in
                                         (match uu____12118 with
                                          | (args,res) ->
                                              let indices =
                                                let uu____12162 =
                                                  let uu____12163 =
                                                    FStar_Syntax_Subst.compress
                                                      res
                                                     in
                                                  uu____12163.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____12162 with
                                                | FStar_Syntax_Syntax.Tm_app
                                                    (uu____12166,indices) ->
                                                    indices
                                                | uu____12192 -> []  in
                                              let env1 =
                                                FStar_All.pipe_right args
                                                  (FStar_List.fold_left
                                                     (fun env1  ->
                                                        fun uu____12222  ->
                                                          match uu____12222
                                                          with
                                                          | (x,uu____12230)
                                                              ->
                                                              let uu____12235
                                                                =
                                                                let uu____12236
                                                                  =
                                                                  let uu____12244
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                  (uu____12244,
                                                                    [xx])
                                                                   in
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  uu____12236
                                                                 in
                                                              FStar_SMTEncoding_Env.push_term_var
                                                                env1 x
                                                                uu____12235)
                                                     env)
                                                 in
                                              let uu____12249 =
                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                  indices env1
                                                 in
                                              (match uu____12249 with
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
                                                       let uu____12274 =
                                                         FStar_List.map2
                                                           (fun v1  ->
                                                              fun a  ->
                                                                let uu____12282
                                                                  =
                                                                  let uu____12287
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                  (uu____12287,
                                                                    a)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____12282)
                                                           vars indices1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____12274
                                                         FStar_SMTEncoding_Util.mk_and_l
                                                        in
                                                     let uu____12290 =
                                                       let uu____12291 =
                                                         let uu____12296 =
                                                           let uu____12297 =
                                                             let uu____12302
                                                               =
                                                               FStar_SMTEncoding_Env.mk_data_tester
                                                                 env1 l xx
                                                                in
                                                             (uu____12302,
                                                               eqs)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____12297
                                                            in
                                                         (out, uu____12296)
                                                          in
                                                       FStar_SMTEncoding_Util.mkOr
                                                         uu____12291
                                                        in
                                                     (uu____12290,
                                                       (FStar_List.append
                                                          decls decls'))))))))
                           (FStar_SMTEncoding_Util.mkFalse, []))
                       in
                    (match uu____12046 with
                     | (data_ax,decls) ->
                         let uu____12315 =
                           FStar_SMTEncoding_Env.fresh_fvar "f"
                             FStar_SMTEncoding_Term.Fuel_sort
                            in
                         (match uu____12315 with
                          | (ffsym,ff) ->
                              let fuel_guarded_inversion =
                                let xx_has_type_sfuel =
                                  if
                                    (FStar_List.length datas) >
                                      (Prims.parse_int "1")
                                  then
                                    let uu____12332 =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [ff])
                                       in
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel
                                      uu____12332 xx tapp
                                  else
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                      xx tapp
                                   in
                                let uu____12339 =
                                  let uu____12347 =
                                    let uu____12348 =
                                      FStar_Ident.range_of_lid t  in
                                    let uu____12349 =
                                      let uu____12360 =
                                        let uu____12361 =
                                          FStar_SMTEncoding_Term.mk_fv
                                            (ffsym,
                                              FStar_SMTEncoding_Term.Fuel_sort)
                                           in
                                        let uu____12363 =
                                          let uu____12366 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          uu____12366 :: vars  in
                                        FStar_SMTEncoding_Env.add_fuel
                                          uu____12361 uu____12363
                                         in
                                      let uu____12368 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (xx_has_type_sfuel, data_ax)
                                         in
                                      ([[xx_has_type_sfuel]], uu____12360,
                                        uu____12368)
                                       in
                                    FStar_SMTEncoding_Term.mkForall
                                      uu____12348 uu____12349
                                     in
                                  let uu____12377 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                      (Prims.strcat "fuel_guarded_inversion_"
                                         t.FStar_Ident.str)
                                     in
                                  (uu____12347,
                                    (FStar_Pervasives_Native.Some
                                       "inversion axiom"), uu____12377)
                                   in
                                FStar_SMTEncoding_Util.mkAssume uu____12339
                                 in
                              FStar_List.append decls
                                [fuel_guarded_inversion])))
              in
           let uu____12383 =
             let uu____12388 =
               let uu____12389 = FStar_Syntax_Subst.compress k  in
               uu____12389.FStar_Syntax_Syntax.n  in
             match uu____12388 with
             | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                 ((FStar_List.append tps formals),
                   (FStar_Syntax_Util.comp_result kres))
             | uu____12424 -> (tps, k)  in
           (match uu____12383 with
            | (formals,res) ->
                let uu____12431 = FStar_Syntax_Subst.open_term formals res
                   in
                (match uu____12431 with
                 | (formals1,res1) ->
                     let uu____12442 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals1 env
                        in
                     (match uu____12442 with
                      | (vars,guards,env',binder_decls,uu____12467) ->
                          let arity = FStar_List.length vars  in
                          let uu____12481 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env t arity
                             in
                          (match uu____12481 with
                           | (tname,ttok,env1) ->
                               let ttok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let tapp =
                                 let uu____12511 =
                                   let uu____12519 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, uu____12519)  in
                                 FStar_SMTEncoding_Util.mkApp uu____12511  in
                               let uu____12525 =
                                 let tname_decl =
                                   let uu____12535 =
                                     let uu____12536 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun fv  ->
                                               let uu____12555 =
                                                 let uu____12557 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     fv
                                                    in
                                                 Prims.strcat tname
                                                   uu____12557
                                                  in
                                               let uu____12559 =
                                                 FStar_SMTEncoding_Term.fv_sort
                                                   fv
                                                  in
                                               (uu____12555, uu____12559,
                                                 false)))
                                        in
                                     let uu____12563 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     (tname, uu____12536,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       uu____12563, false)
                                      in
                                   constructor_or_logic_type_decl uu____12535
                                    in
                                 let uu____12571 =
                                   match vars with
                                   | [] ->
                                       let uu____12584 =
                                         let uu____12585 =
                                           let uu____12588 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tname, [])
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_3  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_3) uu____12588
                                            in
                                         FStar_SMTEncoding_Env.push_free_var
                                           env1 t arity tname uu____12585
                                          in
                                       ([], uu____12584)
                                   | uu____12600 ->
                                       let ttok_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (ttok, [],
                                             FStar_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token"))
                                          in
                                       let ttok_fresh =
                                         let uu____12610 =
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                             ()
                                            in
                                         FStar_SMTEncoding_Term.fresh_token
                                           (ttok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                           uu____12610
                                          in
                                       let ttok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars
                                          in
                                       let pats = [[ttok_app]; [tapp]]  in
                                       let name_tok_corr =
                                         let uu____12626 =
                                           let uu____12634 =
                                             let uu____12635 =
                                               FStar_Ident.range_of_lid t  in
                                             let uu____12636 =
                                               let uu____12652 =
                                                 FStar_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp)
                                                  in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 vars, uu____12652)
                                                in
                                             FStar_SMTEncoding_Term.mkForall'
                                               uu____12635 uu____12636
                                              in
                                           (uu____12634,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.strcat
                                                "token_correspondence_" ttok))
                                            in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____12626
                                          in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env1)
                                    in
                                 match uu____12571 with
                                 | (tok_decls,env2) ->
                                     let uu____12679 =
                                       FStar_Ident.lid_equals t
                                         FStar_Parser_Const.lex_t_lid
                                        in
                                     if uu____12679
                                     then (tok_decls, env2)
                                     else
                                       ((FStar_List.append tname_decl
                                           tok_decls), env2)
                                  in
                               (match uu____12525 with
                                | (decls,env2) ->
                                    let kindingAx =
                                      let uu____12707 =
                                        FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res1
                                          env' tapp
                                         in
                                      match uu____12707 with
                                      | (k1,decls1) ->
                                          let karr =
                                            if
                                              (FStar_List.length formals1) >
                                                (Prims.parse_int "0")
                                            then
                                              let uu____12729 =
                                                let uu____12730 =
                                                  let uu____12738 =
                                                    let uu____12739 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____12739
                                                     in
                                                  (uu____12738,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.strcat
                                                       "pre_kinding_" ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____12730
                                                 in
                                              [uu____12729]
                                            else []  in
                                          let uu____12747 =
                                            let uu____12750 =
                                              let uu____12753 =
                                                let uu____12754 =
                                                  let uu____12762 =
                                                    let uu____12763 =
                                                      FStar_Ident.range_of_lid
                                                        t
                                                       in
                                                    let uu____12764 =
                                                      let uu____12775 =
                                                        FStar_SMTEncoding_Util.mkImp
                                                          (guard, k1)
                                                         in
                                                      ([[tapp]], vars,
                                                        uu____12775)
                                                       in
                                                    FStar_SMTEncoding_Term.mkForall
                                                      uu____12763 uu____12764
                                                     in
                                                  (uu____12762,
                                                    FStar_Pervasives_Native.None,
                                                    (Prims.strcat "kinding_"
                                                       ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____12754
                                                 in
                                              [uu____12753]  in
                                            FStar_List.append karr
                                              uu____12750
                                             in
                                          FStar_List.append decls1
                                            uu____12747
                                       in
                                    let aux =
                                      let uu____12790 =
                                        let uu____12793 =
                                          inversion_axioms tapp vars  in
                                        let uu____12796 =
                                          let uu____12799 =
                                            let uu____12800 =
                                              FStar_Ident.range_of_lid t  in
                                            pretype_axiom uu____12800 env2
                                              tapp vars
                                             in
                                          [uu____12799]  in
                                        FStar_List.append uu____12793
                                          uu____12796
                                         in
                                      FStar_List.append kindingAx uu____12790
                                       in
                                    let g =
                                      FStar_List.append decls
                                        (FStar_List.append binder_decls aux)
                                       in
                                    (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____12805,uu____12806,uu____12807,uu____12808,uu____12809)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____12817,t,uu____12819,n_tps,uu____12821) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____12831 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____12831 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____12879 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____12879 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____12907 =
                       FStar_SMTEncoding_Env.fresh_fvar "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____12907 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____12927 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____12927 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____13006 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____13006,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____13013 =
                                   let uu____13014 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____13014, true)
                                    in
                                 let uu____13022 =
                                   let uu____13029 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____13029
                                    in
                                 FStar_All.pipe_right uu____13013 uu____13022
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
                               let uu____13041 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____13041 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____13053::uu____13054 ->
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
                                            let uu____13103 =
                                              let uu____13104 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____13104]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____13103
                                             in
                                          let uu____13130 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____13131 =
                                            let uu____13142 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____13142)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____13130 uu____13131
                                      | uu____13169 -> tok_typing  in
                                    let uu____13180 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____13180 with
                                     | (vars',guards',env'',decls_formals,uu____13205)
                                         ->
                                         let uu____13218 =
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
                                         (match uu____13218 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____13248 ->
                                                    let uu____13257 =
                                                      let uu____13258 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____13258
                                                       in
                                                    [uu____13257]
                                                 in
                                              let encode_elim uu____13274 =
                                                let uu____13275 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____13275 with
                                                | (head1,args) ->
                                                    let uu____13326 =
                                                      let uu____13327 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____13327.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____13326 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13339;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13340;_},uu____13341)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____13347 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____13347
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
                                                                  | uu____13410
                                                                    ->
                                                                    let uu____13411
                                                                    =
                                                                    let uu____13417
                                                                    =
                                                                    let uu____13419
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13419
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13417)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13411
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13442
                                                                    =
                                                                    let uu____13444
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13444
                                                                     in
                                                                    if
                                                                    uu____13442
                                                                    then
                                                                    let uu____13466
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13466]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____13469
                                                                =
                                                                let uu____13483
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____13540
                                                                     ->
                                                                    fun
                                                                    uu____13541
                                                                     ->
                                                                    match 
                                                                    (uu____13540,
                                                                    uu____13541)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13652
                                                                    =
                                                                    let uu____13660
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13660
                                                                     in
                                                                    (match uu____13652
                                                                    with
                                                                    | 
                                                                    (uu____13674,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13685
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13685
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13690
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13690
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
                                                                  uu____13483
                                                                 in
                                                              (match uu____13469
                                                               with
                                                               | (uu____13711,arg_vars,elim_eqns_or_guards,uu____13714)
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
                                                                    let uu____13741
                                                                    =
                                                                    let uu____13749
                                                                    =
                                                                    let uu____13750
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13751
                                                                    =
                                                                    let uu____13762
                                                                    =
                                                                    let uu____13763
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____13763
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13765
                                                                    =
                                                                    let uu____13766
                                                                    =
                                                                    let uu____13771
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13771)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13766
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13762,
                                                                    uu____13765)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13750
                                                                    uu____13751
                                                                     in
                                                                    (uu____13749,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13741
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13786
                                                                    =
                                                                    let uu____13787
                                                                    =
                                                                    let uu____13793
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13793,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____13787
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13786
                                                                     in
                                                                    let uu____13796
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13796
                                                                    then
                                                                    let x =
                                                                    let uu____13800
                                                                    =
                                                                    let uu____13806
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13806,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____13800
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13811
                                                                    =
                                                                    let uu____13819
                                                                    =
                                                                    let uu____13820
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13821
                                                                    =
                                                                    let uu____13832
                                                                    =
                                                                    let uu____13837
                                                                    =
                                                                    let uu____13840
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13840]
                                                                     in
                                                                    [uu____13837]
                                                                     in
                                                                    let uu____13845
                                                                    =
                                                                    let uu____13846
                                                                    =
                                                                    let uu____13851
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13851,
                                                                    uu____13853)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13846
                                                                     in
                                                                    (uu____13832,
                                                                    [x],
                                                                    uu____13845)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13820
                                                                    uu____13821
                                                                     in
                                                                    let uu____13874
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13819,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13874)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13811
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13885
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
                                                                    (let uu____13908
                                                                    =
                                                                    let uu____13909
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____13909
                                                                    dapp1  in
                                                                    [uu____13908])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13885
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____13916
                                                                    =
                                                                    let uu____13924
                                                                    =
                                                                    let uu____13925
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13926
                                                                    =
                                                                    let uu____13937
                                                                    =
                                                                    let uu____13938
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____13938
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13940
                                                                    =
                                                                    let uu____13941
                                                                    =
                                                                    let uu____13946
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____13946)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13941
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13937,
                                                                    uu____13940)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13925
                                                                    uu____13926
                                                                     in
                                                                    (uu____13924,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13916)
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
                                                         let uu____13965 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____13965
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
                                                                  | uu____14028
                                                                    ->
                                                                    let uu____14029
                                                                    =
                                                                    let uu____14035
                                                                    =
                                                                    let uu____14037
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14037
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14035)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14029
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14060
                                                                    =
                                                                    let uu____14062
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14062
                                                                     in
                                                                    if
                                                                    uu____14060
                                                                    then
                                                                    let uu____14084
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14084]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14087
                                                                =
                                                                let uu____14101
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14158
                                                                     ->
                                                                    fun
                                                                    uu____14159
                                                                     ->
                                                                    match 
                                                                    (uu____14158,
                                                                    uu____14159)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14270
                                                                    =
                                                                    let uu____14278
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14278
                                                                     in
                                                                    (match uu____14270
                                                                    with
                                                                    | 
                                                                    (uu____14292,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14303
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14303
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14308
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
                                                                  uu____14101
                                                                 in
                                                              (match uu____14087
                                                               with
                                                               | (uu____14329,arg_vars,elim_eqns_or_guards,uu____14332)
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
                                                                    let uu____14359
                                                                    =
                                                                    let uu____14367
                                                                    =
                                                                    let uu____14368
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14369
                                                                    =
                                                                    let uu____14380
                                                                    =
                                                                    let uu____14381
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14381
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14383
                                                                    =
                                                                    let uu____14384
                                                                    =
                                                                    let uu____14389
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14389)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14384
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14380,
                                                                    uu____14383)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14368
                                                                    uu____14369
                                                                     in
                                                                    (uu____14367,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14359
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14404
                                                                    =
                                                                    let uu____14405
                                                                    =
                                                                    let uu____14411
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14411,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14405
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14404
                                                                     in
                                                                    let uu____14414
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14414
                                                                    then
                                                                    let x =
                                                                    let uu____14418
                                                                    =
                                                                    let uu____14424
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14424,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14418
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14429
                                                                    =
                                                                    let uu____14437
                                                                    =
                                                                    let uu____14438
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14439
                                                                    =
                                                                    let uu____14450
                                                                    =
                                                                    let uu____14455
                                                                    =
                                                                    let uu____14458
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14458]
                                                                     in
                                                                    [uu____14455]
                                                                     in
                                                                    let uu____14463
                                                                    =
                                                                    let uu____14464
                                                                    =
                                                                    let uu____14469
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14471
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14469,
                                                                    uu____14471)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14464
                                                                     in
                                                                    (uu____14450,
                                                                    [x],
                                                                    uu____14463)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14438
                                                                    uu____14439
                                                                     in
                                                                    let uu____14492
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14437,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14492)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14429
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14503
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
                                                                    (let uu____14526
                                                                    =
                                                                    let uu____14527
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14527
                                                                    dapp1  in
                                                                    [uu____14526])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14503
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14542
                                                                    =
                                                                    let uu____14543
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14544
                                                                    =
                                                                    let uu____14555
                                                                    =
                                                                    let uu____14556
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14556
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14558
                                                                    =
                                                                    let uu____14559
                                                                    =
                                                                    let uu____14564
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14564)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14559
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14555,
                                                                    uu____14558)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14543
                                                                    uu____14544
                                                                     in
                                                                    (uu____14542,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14534)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____14581 ->
                                                         ((let uu____14583 =
                                                             let uu____14589
                                                               =
                                                               let uu____14591
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____14593
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____14591
                                                                 uu____14593
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____14589)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____14583);
                                                          ([], [])))
                                                 in
                                              let uu____14601 =
                                                encode_elim ()  in
                                              (match uu____14601 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____14627 =
                                                       let uu____14630 =
                                                         let uu____14633 =
                                                           let uu____14636 =
                                                             let uu____14639
                                                               =
                                                               let uu____14640
                                                                 =
                                                                 let uu____14652
                                                                   =
                                                                   let uu____14653
                                                                    =
                                                                    let uu____14655
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14655
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____14653
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   uu____14652)
                                                                  in
                                                               FStar_SMTEncoding_Term.DeclFun
                                                                 uu____14640
                                                                in
                                                             [uu____14639]
                                                              in
                                                           let uu____14662 =
                                                             let uu____14665
                                                               =
                                                               let uu____14668
                                                                 =
                                                                 let uu____14671
                                                                   =
                                                                   let uu____14674
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14685
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14694
                                                                    =
                                                                    let uu____14695
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14696
                                                                    =
                                                                    let uu____14707
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14707)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14695
                                                                    uu____14696
                                                                     in
                                                                    (uu____14694,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14686
                                                                     in
                                                                    let uu____14720
                                                                    =
                                                                    let uu____14723
                                                                    =
                                                                    let uu____14724
                                                                    =
                                                                    let uu____14732
                                                                    =
                                                                    let uu____14733
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14734
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    let uu____14746
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14746
                                                                    vars'  in
                                                                    let uu____14748
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14745,
                                                                    uu____14748)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14733
                                                                    uu____14734
                                                                     in
                                                                    (uu____14732,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14724
                                                                     in
                                                                    [uu____14723]
                                                                     in
                                                                    uu____14685
                                                                    ::
                                                                    uu____14720
                                                                     in
                                                                    uu____14677
                                                                    ::
                                                                    uu____14682
                                                                     in
                                                                   FStar_List.append
                                                                    uu____14674
                                                                    elim
                                                                    in
                                                                 FStar_List.append
                                                                   decls_pred
                                                                   uu____14671
                                                                  in
                                                               FStar_List.append
                                                                 decls_formals
                                                                 uu____14668
                                                                in
                                                             FStar_List.append
                                                               proxy_fresh
                                                               uu____14665
                                                              in
                                                           FStar_List.append
                                                             uu____14636
                                                             uu____14662
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____14633
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____14630
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____14627
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
           (fun uu____14786  ->
              fun se  ->
                match uu____14786 with
                | (g,env1) ->
                    let uu____14806 = encode_sigelt env1 se  in
                    (match uu____14806 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14874 =
        match uu____14874 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____14911 ->
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
                 ((let uu____14919 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14919
                   then
                     let uu____14924 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14926 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14928 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14924 uu____14926 uu____14928
                   else ());
                  (let uu____14933 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____14933 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14951 =
                         let uu____14959 =
                           let uu____14961 =
                             let uu____14963 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____14963
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____14961  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____14959
                          in
                       (match uu____14951 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____14983 = FStar_Options.log_queries ()
                                 in
                              if uu____14983
                              then
                                let uu____14986 =
                                  let uu____14988 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14990 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14992 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14988 uu____14990 uu____14992
                                   in
                                FStar_Pervasives_Native.Some uu____14986
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15016,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15036 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15036 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15063 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15063 with | (uu____15090,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15143  ->
              match uu____15143 with
              | (l,uu____15152,uu____15153) ->
                  let uu____15156 =
                    let uu____15168 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____15168, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____15156))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15201  ->
              match uu____15201 with
              | (l,uu____15212,uu____15213) ->
                  let uu____15216 =
                    let uu____15217 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____15217
                     in
                  let uu____15220 =
                    let uu____15223 =
                      let uu____15224 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15224  in
                    [uu____15223]  in
                  uu____15216 :: uu____15220))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15253 =
      let uu____15256 =
        let uu____15257 = FStar_Util.psmap_empty ()  in
        let uu____15272 = FStar_Util.psmap_empty ()  in
        let uu____15275 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15279 =
          let uu____15281 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15281 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15257;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15272;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____15275;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15279;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____15256]  in
    FStar_ST.op_Colon_Equals last_env uu____15253
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15323 = FStar_ST.op_Bang last_env  in
      match uu____15323 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15351 ->
          let uu___397_15354 = e  in
          let uu____15355 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___397_15354.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___397_15354.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___397_15354.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___397_15354.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___397_15354.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___397_15354.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___397_15354.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___397_15354.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15355;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___397_15354.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15363 = FStar_ST.op_Bang last_env  in
    match uu____15363 with
    | [] -> failwith "Empty env stack"
    | uu____15390::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15422  ->
    let uu____15423 = FStar_ST.op_Bang last_env  in
    match uu____15423 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15483  ->
    let uu____15484 = FStar_ST.op_Bang last_env  in
    match uu____15484 with
    | [] -> failwith "Popping an empty stack"
    | uu____15511::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15548  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15601  ->
         let uu____15602 = snapshot_env ()  in
         match uu____15602 with
         | (env_depth,()) ->
             let uu____15624 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____15624 with
              | (varops_depth,()) ->
                  let uu____15646 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____15646 with
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
        (fun uu____15704  ->
           let uu____15705 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____15705 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____15800 = snapshot msg  in () 
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
        | (uu____15846::uu____15847,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___398_15855 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___398_15855.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___398_15855.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___398_15855.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15856 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____15876 =
        let uu____15879 =
          let uu____15880 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____15880  in
        let uu____15881 = open_fact_db_tags env  in uu____15879 ::
          uu____15881
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15876
  
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
      let uu____15908 = encode_sigelt env se  in
      match uu____15908 with
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
        let uu____15953 = FStar_Options.log_queries ()  in
        if uu____15953
        then
          let uu____15958 =
            let uu____15959 =
              let uu____15961 =
                let uu____15963 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15963 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15961  in
            FStar_SMTEncoding_Term.Caption uu____15959  in
          uu____15958 :: decls
        else decls  in
      (let uu____15982 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____15982
       then
         let uu____15985 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____15985
       else ());
      (let env =
         let uu____15991 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____15991 tcenv  in
       let uu____15992 = encode_top_level_facts env se  in
       match uu____15992 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16006 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16006)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16020 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16020
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16035 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____16035
          then
            let uu____16038 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16038
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16084  ->
                    fun se  ->
                      match uu____16084 with
                      | (g,env2) ->
                          let uu____16104 = encode_top_level_facts env2 se
                             in
                          (match uu____16104 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16127 =
            encode_signature
              (let uu___399_16136 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___399_16136.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___399_16136.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___399_16136.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___399_16136.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___399_16136.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___399_16136.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___399_16136.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___399_16136.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___399_16136.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___399_16136.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16127 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____16156 = FStar_Options.log_queries ()  in
                if uu____16156
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
                 (let uu___400_16176 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___400_16176.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___400_16176.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___400_16176.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___400_16176.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___400_16176.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___400_16176.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___400_16176.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___400_16176.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___400_16176.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___400_16176.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____16179 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16179
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
        (let uu____16244 =
           let uu____16246 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16246.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16244);
        (let env =
           let uu____16248 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16248 tcenv  in
         let uu____16249 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16288 = aux rest  in
                 (match uu____16288 with
                  | (out,rest1) ->
                      let t =
                        let uu____16316 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16316 with
                        | FStar_Pervasives_Native.Some uu____16319 ->
                            let uu____16320 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16320
                              x.FStar_Syntax_Syntax.sort
                        | uu____16321 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16325 =
                        let uu____16328 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___401_16331 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___401_16331.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___401_16331.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16328 :: out  in
                      (uu____16325, rest1))
             | uu____16336 -> ([], bindings)  in
           let uu____16343 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16343 with
           | (closing,bindings) ->
               let uu____16370 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16370, bindings)
            in
         match uu____16249 with
         | (q1,bindings) ->
             let uu____16401 = encode_env_bindings env bindings  in
             (match uu____16401 with
              | (env_decls,env1) ->
                  ((let uu____16423 =
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
                    if uu____16423
                    then
                      let uu____16430 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16430
                    else ());
                   (let uu____16435 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16435 with
                    | (phi,qdecls) ->
                        let uu____16456 =
                          let uu____16461 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16461 phi
                           in
                        (match uu____16456 with
                         | (labels,phi1) ->
                             let uu____16478 = encode_labels labels  in
                             (match uu____16478 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____16514 =
                                      FStar_Options.log_queries ()  in
                                    if uu____16514
                                    then
                                      let uu____16519 =
                                        let uu____16520 =
                                          let uu____16522 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____16522
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____16520
                                         in
                                      [uu____16519]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____16531 =
                                      let uu____16539 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16540 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____16539,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16540)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16531
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
  