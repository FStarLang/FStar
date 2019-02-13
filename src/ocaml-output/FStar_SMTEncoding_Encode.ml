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
                                  (let uu___391_5531 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___391_5531.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___391_5531.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___391_5531.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___391_5531.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___391_5531.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___391_5531.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___391_5531.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___391_5531.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___391_5531.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___391_5531.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___391_5531.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___391_5531.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___391_5531.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___391_5531.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___391_5531.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___391_5531.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___391_5531.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___391_5531.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___391_5531.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___391_5531.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___391_5531.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___391_5531.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___391_5531.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___391_5531.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___391_5531.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___391_5531.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___391_5531.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___391_5531.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___391_5531.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___391_5531.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___391_5531.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___391_5531.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___391_5531.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___391_5531.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___391_5531.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___391_5531.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___391_5531.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___391_5531.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___391_5531.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___391_5531.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___391_5531.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___391_5531.FStar_TypeChecker_Env.nbe)
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
                               (fun uu___381_5662  ->
                                  match uu___381_5662 with
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
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____6105 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____6105))
                                       &&
                                       (let uu____6111 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____6111))
                                      &&
                                      (let uu____6114 = is_type1 t_norm  in
                                       Prims.op_Negation uu____6114)
                                     in
                                  let uu____6116 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____6175 -> (false, vars)  in
                                  (match uu____6116 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____6227 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____6227 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____6265 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____6274 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____6274
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____6285 ->
                                                  let uu____6294 =
                                                    let uu____6302 =
                                                      get_vtok ()  in
                                                    (uu____6302, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6294
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____6309 =
                                                let uu____6317 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____6317)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____6309
                                               in
                                            let uu____6331 =
                                              let vname_decl =
                                                let uu____6339 =
                                                  let uu____6351 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____6351,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____6339
                                                 in
                                              let uu____6362 =
                                                let env2 =
                                                  let uu___392_6368 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.cache
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.cache);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___392_6368.FStar_SMTEncoding_Env.encoding_quantifier)
                                                  }  in
                                                let uu____6369 =
                                                  let uu____6371 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____6371
                                                   in
                                                if uu____6369
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____6362 with
                                              | (tok_typing,decls2) ->
                                                  let uu____6388 =
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
                                                        let uu____6414 =
                                                          let uu____6415 =
                                                            let uu____6418 =
                                                              let uu____6419
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____6419
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____6418
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____6415
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [tok_typing1]),
                                                          uu____6414)
                                                    | uu____6429 when thunked
                                                        ->
                                                        let uu____6440 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____6440
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
                                                                 ("FStar.Pervasives.ambient",
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
                                                  (match uu____6388 with
                                                   | (tok_decl,env2) ->
                                                       ((vname_decl ::
                                                         tok_decl), env2))
                                               in
                                            (match uu____6331 with
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
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl
            Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____6836 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6836 with
          | FStar_Pervasives_Native.None  ->
              let uu____6847 = encode_free_var false env x t t_norm []  in
              (match uu____6847 with
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
            let uu____6918 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6918 with
            | (decls,env1) ->
                let uu____6937 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6937
                then
                  let uu____6946 =
                    let uu____6949 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6949  in
                  (uu____6946, env1)
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
             (fun uu____7009  ->
                fun lb  ->
                  match uu____7009 with
                  | (decls,env1) ->
                      let uu____7029 =
                        let uu____7036 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7036
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7029 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7069 = FStar_Syntax_Util.head_and_args t  in
    match uu____7069 with
    | (hd1,args) ->
        let uu____7113 =
          let uu____7114 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7114.FStar_Syntax_Syntax.n  in
        (match uu____7113 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7120,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7144 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7155 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___393_7163 = en  in
    let uu____7164 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___393_7163.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___393_7163.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___393_7163.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___393_7163.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___393_7163.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7164;
      FStar_SMTEncoding_Env.nolabels =
        (uu___393_7163.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___393_7163.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___393_7163.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___393_7163.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___393_7163.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7196  ->
      fun quals  ->
        match uu____7196 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7303 = FStar_Util.first_N nbinders formals  in
              match uu____7303 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7404  ->
                         fun uu____7405  ->
                           match (uu____7404, uu____7405) with
                           | ((formal,uu____7431),(binder,uu____7433)) ->
                               let uu____7454 =
                                 let uu____7461 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7461)  in
                               FStar_Syntax_Syntax.NT uu____7454) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7475 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7516  ->
                              match uu____7516 with
                              | (x,i) ->
                                  let uu____7535 =
                                    let uu___394_7536 = x  in
                                    let uu____7537 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___394_7536.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___394_7536.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7537
                                    }  in
                                  (uu____7535, i)))
                       in
                    FStar_All.pipe_right uu____7475
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7561 =
                      let uu____7566 = FStar_Syntax_Subst.compress body  in
                      let uu____7567 =
                        let uu____7568 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7568
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7566 uu____7567
                       in
                    uu____7561 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___395_7619 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___395_7619.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___395_7619.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___395_7619.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___395_7619.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___395_7619.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___395_7619.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___395_7619.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___395_7619.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___395_7619.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___395_7619.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___395_7619.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___395_7619.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___395_7619.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___395_7619.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___395_7619.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___395_7619.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___395_7619.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___395_7619.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___395_7619.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___395_7619.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___395_7619.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___395_7619.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___395_7619.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___395_7619.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___395_7619.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___395_7619.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___395_7619.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___395_7619.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___395_7619.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___395_7619.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___395_7619.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___395_7619.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___395_7619.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___395_7619.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___395_7619.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___395_7619.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___395_7619.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___395_7619.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___395_7619.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___395_7619.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___395_7619.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___395_7619.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7691  ->
                       fun uu____7692  ->
                         match (uu____7691, uu____7692) with
                         | ((x,uu____7718),(b,uu____7720)) ->
                             let uu____7741 =
                               let uu____7748 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7748)  in
                             FStar_Syntax_Syntax.NT uu____7741) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7773 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7773
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7802 ->
                    let uu____7809 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7809
                | uu____7810 when Prims.op_Negation norm1 ->
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
                | uu____7813 ->
                    let uu____7814 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7814)
                 in
              let aux t1 e1 =
                let uu____7856 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7856 with
                | (binders,body,lopt) ->
                    let uu____7888 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7904 -> arrow_formals_comp_norm false t1  in
                    (match uu____7888 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7938 =
                           if nformals < nbinders
                           then
                             let uu____7982 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7982 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____8066 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____8066)
                           else
                             if nformals > nbinders
                             then
                               (let uu____8106 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____8106 with
                                | (binders1,body1) ->
                                    let uu____8159 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____8159))
                             else
                               (let uu____8172 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____8172))
                            in
                         (match uu____7938 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____8232 = aux t e  in
              match uu____8232 with
              | (binders,body,comp) ->
                  let uu____8278 =
                    let uu____8289 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____8289
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____8304 = aux comp1 body1  in
                      match uu____8304 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____8278 with
                   | (binders1,body1,comp1) ->
                       let uu____8387 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____8387, comp1))
               in
            (try
               (fun uu___397_8414  ->
                  match () with
                  | () ->
                      let uu____8421 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8421
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8437 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8500  ->
                                   fun lb  ->
                                     match uu____8500 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8555 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8555
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8561 =
                                             let uu____8570 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8570
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8561 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8437 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____8711;
                                    FStar_Syntax_Syntax.lbeff = uu____8712;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8714;
                                    FStar_Syntax_Syntax.lbpos = uu____8715;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8739 =
                                     let uu____8746 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8746 with
                                     | (tcenv',uu____8762,e_t) ->
                                         let uu____8768 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8779 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8768 with
                                          | (e1,t_norm1) ->
                                              ((let uu___398_8796 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___398_8796.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8739 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8806 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____8806 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8826 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8826
                                               then
                                                 let uu____8831 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8834 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8831 uu____8834
                                               else ());
                                              (let uu____8839 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8839 with
                                               | (vars,_guards,env'1,binder_decls,uu____8866)
                                                   ->
                                                   let uu____8879 =
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
                                                         let uu____8896 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____8896
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____8918 =
                                                          let uu____8919 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____8920 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____8919 fvb
                                                            uu____8920
                                                           in
                                                        (vars, uu____8918))
                                                      in
                                                   (match uu____8879 with
                                                    | (vars1,app) ->
                                                        let uu____8931 =
                                                          let is_logical =
                                                            let uu____8944 =
                                                              let uu____8945
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____8945.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____8944
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____8951 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____8955 =
                                                              let uu____8956
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8956
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____8955
                                                              (fun lid  ->
                                                                 let uu____8965
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____8965
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____8966 =
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
                                                          if uu____8966
                                                          then
                                                            let uu____8982 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____8983 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app, uu____8982,
                                                              uu____8983)
                                                          else
                                                            (let uu____8994 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____8994))
                                                           in
                                                        (match uu____8931
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____9018
                                                                 =
                                                                 let uu____9026
                                                                   =
                                                                   let uu____9027
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____9028
                                                                    =
                                                                    let uu____9039
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____9039)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____9027
                                                                    uu____9028
                                                                    in
                                                                 let uu____9048
                                                                   =
                                                                   let uu____9049
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9049
                                                                    in
                                                                 (uu____9026,
                                                                   uu____9048,
                                                                   (Prims.strcat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____9018
                                                                in
                                                             let uu____9055 =
                                                               let uu____9058
                                                                 =
                                                                 let uu____9061
                                                                   =
                                                                   let uu____9064
                                                                    =
                                                                    let uu____9067
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    FStar_List.append
                                                                    [eqn]
                                                                    uu____9067
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____9064
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____9061
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____9058
                                                                in
                                                             (uu____9055,
                                                               env2)))))))
                               | uu____9072 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9132 =
                                   let uu____9138 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       "fuel"
                                      in
                                   (uu____9138,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____9132  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9144 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9197  ->
                                         fun fvb  ->
                                           match uu____9197 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9252 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9252
                                                  in
                                               let gtok =
                                                 let uu____9256 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9256
                                                  in
                                               let env4 =
                                                 let uu____9259 =
                                                   let uu____9262 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9262
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9259
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9144 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9389
                                     t_norm uu____9391 =
                                     match (uu____9389, uu____9391) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9423;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9424;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9426;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9427;_})
                                         ->
                                         let uu____9454 =
                                           let uu____9461 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9461 with
                                           | (tcenv',uu____9477,e_t) ->
                                               let uu____9483 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9494 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9483 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___399_9511 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___399_9511.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9454 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9526 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9526
                                                then
                                                  let uu____9531 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9533 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9535 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9531 uu____9533
                                                    uu____9535
                                                else ());
                                               (let uu____9540 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____9540 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9569 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9569 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9593 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9593
                                                           then
                                                             let uu____9598 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9600 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9603 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9605 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9598
                                                               uu____9600
                                                               uu____9603
                                                               uu____9605
                                                           else ());
                                                          (let uu____9610 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9610
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9641)
                                                               ->
                                                               let uu____9654
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9667
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9667,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9671
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9671
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9684
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9684,
                                                                    decls0))
                                                                  in
                                                               (match uu____9654
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
                                                                    let uu____9707
                                                                    =
                                                                    let uu____9719
                                                                    =
                                                                    let uu____9722
                                                                    =
                                                                    let uu____9725
                                                                    =
                                                                    let uu____9728
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9728
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____9725
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9722
                                                                     in
                                                                    (g,
                                                                    uu____9719,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9707
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
                                                                    let uu____9758
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9758
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
                                                                    let uu____9773
                                                                    =
                                                                    let uu____9776
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9776
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9773
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9782
                                                                    =
                                                                    let uu____9785
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9785
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9782
                                                                     in
                                                                    let uu____9790
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9790
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9808
                                                                    =
                                                                    let uu____9816
                                                                    =
                                                                    let uu____9817
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9818
                                                                    =
                                                                    let uu____9834
                                                                    =
                                                                    let uu____9835
                                                                    =
                                                                    let uu____9840
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9840)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9835
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9834)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9817
                                                                    uu____9818
                                                                     in
                                                                    let uu____9854
                                                                    =
                                                                    let uu____9855
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9855
                                                                     in
                                                                    (uu____9816,
                                                                    uu____9854,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9808
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9862
                                                                    =
                                                                    let uu____9870
                                                                    =
                                                                    let uu____9871
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9872
                                                                    =
                                                                    let uu____9883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9883)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9871
                                                                    uu____9872
                                                                     in
                                                                    (uu____9870,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9862
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9897
                                                                    =
                                                                    let uu____9905
                                                                    =
                                                                    let uu____9906
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9907
                                                                    =
                                                                    let uu____9918
                                                                    =
                                                                    let uu____9919
                                                                    =
                                                                    let uu____9924
                                                                    =
                                                                    let uu____9925
                                                                    =
                                                                    let uu____9928
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9928
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9925
                                                                     in
                                                                    (gsapp,
                                                                    uu____9924)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9919
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9918)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9906
                                                                    uu____9907
                                                                     in
                                                                    (uu____9905,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9897
                                                                     in
                                                                    let uu____9942
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
                                                                    let uu____9954
                                                                    =
                                                                    let uu____9955
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____9955
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9954
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9957
                                                                    =
                                                                    let uu____9965
                                                                    =
                                                                    let uu____9966
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9967
                                                                    =
                                                                    let uu____9978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9978)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9966
                                                                    uu____9967
                                                                     in
                                                                    (uu____9965,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9957
                                                                     in
                                                                    let uu____9991
                                                                    =
                                                                    let uu____10000
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____10000
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10015
                                                                    =
                                                                    let uu____10018
                                                                    =
                                                                    let uu____10019
                                                                    =
                                                                    let uu____10027
                                                                    =
                                                                    let uu____10028
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10029
                                                                    =
                                                                    let uu____10040
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10040)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10028
                                                                    uu____10029
                                                                     in
                                                                    (uu____10027,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10019
                                                                     in
                                                                    [uu____10018]
                                                                     in
                                                                    (d3,
                                                                    uu____10015)
                                                                     in
                                                                    match uu____9991
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9942
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
                                   let uu____10103 =
                                     let uu____10116 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10179  ->
                                          fun uu____10180  ->
                                            match (uu____10179, uu____10180)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10305 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10305 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10116
                                      in
                                   (match uu____10103 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10378 =
                                          let isDeclFun uu___382_10393 =
                                            match uu___382_10393 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10395 -> true
                                            | uu____10408 -> false  in
                                          let uu____10410 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10410
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____10378 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10450 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___383_10456  ->
                                        match uu___383_10456 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10459 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10467 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10467)))
                                in
                             if uu____10450
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___401_10489  ->
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
                   let uu____10527 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10527
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
        let uu____10597 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10597 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10603 = encode_sigelt' env se  in
      match uu____10603 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10615 =
                  let uu____10616 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____10616  in
                [uu____10615]
            | uu____10619 ->
                let uu____10620 =
                  let uu____10623 =
                    let uu____10624 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10624  in
                  uu____10623 :: g  in
                let uu____10627 =
                  let uu____10630 =
                    let uu____10631 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10631  in
                  [uu____10630]  in
                FStar_List.append uu____10620 uu____10627
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____10641 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____10641
       then
         let uu____10646 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____10646
       else ());
      (let is_opaque_to_smt t =
         let uu____10658 =
           let uu____10659 = FStar_Syntax_Subst.compress t  in
           uu____10659.FStar_Syntax_Syntax.n  in
         match uu____10658 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10664)) -> s = "opaque_to_smt"
         | uu____10669 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____10678 =
           let uu____10679 = FStar_Syntax_Subst.compress t  in
           uu____10679.FStar_Syntax_Syntax.n  in
         match uu____10678 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____10684)) -> s = "uninterpreted_by_smt"
         | uu____10689 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10695 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____10701 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____10713 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____10714 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10715 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____10728 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____10730 =
             let uu____10732 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____10732  in
           if uu____10730
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____10761 ->
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
                let uu____10793 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____10793 with
                | (formals,uu____10813) ->
                    let arity = FStar_List.length formals  in
                    let uu____10837 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____10837 with
                     | (aname,atok,env2) ->
                         let uu____10863 =
                           let uu____10868 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____10868 env2
                            in
                         (match uu____10863 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____10880 =
                                  let uu____10881 =
                                    let uu____10893 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____10913  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____10893,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____10881
                                   in
                                [uu____10880;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____10930 =
                                let aux uu____10976 uu____10977 =
                                  match (uu____10976, uu____10977) with
                                  | ((bv,uu____11021),(env3,acc_sorts,acc))
                                      ->
                                      let uu____11053 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____11053 with
                                       | (xxsym,xx,env4) ->
                                           let uu____11076 =
                                             let uu____11079 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____11079 :: acc_sorts  in
                                           (env4, uu____11076, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____10930 with
                               | (uu____11111,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____11127 =
                                       let uu____11135 =
                                         let uu____11136 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11137 =
                                           let uu____11148 =
                                             let uu____11149 =
                                               let uu____11154 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____11154)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____11149
                                              in
                                           ([[app]], xs_sorts, uu____11148)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11136 uu____11137
                                          in
                                       (uu____11135,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.strcat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11127
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____11169 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____11169
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____11172 =
                                       let uu____11180 =
                                         let uu____11181 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11182 =
                                           let uu____11193 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____11193)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11181 uu____11182
                                          in
                                       (uu____11180,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.strcat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11172
                                      in
                                   (env2,
                                     (FStar_List.append decls
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence]))))))
                 in
              let uu____11208 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____11208 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11234,uu____11235)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____11236 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____11236 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11258,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____11265 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___384_11271  ->
                       match uu___384_11271 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____11274 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11280 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____11283 -> false))
                in
             Prims.op_Negation uu____11265  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____11293 =
                let uu____11300 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____11300 env fv t quals  in
              match uu____11293 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____11318 =
                      FStar_SMTEncoding_Term.mk_fv
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____11318
                     in
                  let uu____11320 =
                    let uu____11321 =
                      primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                        lid tname tsym
                       in
                    FStar_List.append decls uu____11321  in
                  (uu____11320, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____11327 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____11327 with
            | (uvs,f1) ->
                let env1 =
                  let uu___402_11339 = env  in
                  let uu____11340 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___402_11339.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___402_11339.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___402_11339.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____11340;
                    FStar_SMTEncoding_Env.warn =
                      (uu___402_11339.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.cache =
                      (uu___402_11339.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___402_11339.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___402_11339.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___402_11339.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___402_11339.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___402_11339.FStar_SMTEncoding_Env.encoding_quantifier)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____11342 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____11342 with
                 | (f3,decls) ->
                     let g =
                       let uu____11356 =
                         let uu____11357 =
                           let uu____11365 =
                             let uu____11366 =
                               let uu____11368 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.format1 "Assumption: %s"
                                 uu____11368
                                in
                             FStar_Pervasives_Native.Some uu____11366  in
                           let uu____11372 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                               (Prims.strcat "assumption_" l.FStar_Ident.str)
                              in
                           (f3, uu____11365, uu____11372)  in
                         FStar_SMTEncoding_Util.mkAssume uu____11357  in
                       [uu____11356]  in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____11377) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____11391 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____11413 =
                        let uu____11416 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____11416.FStar_Syntax_Syntax.fv_name  in
                      uu____11413.FStar_Syntax_Syntax.v  in
                    let uu____11417 =
                      let uu____11419 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____11419  in
                    if uu____11417
                    then
                      let val_decl =
                        let uu___403_11451 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___403_11451.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___403_11451.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___403_11451.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____11452 = encode_sigelt' env1 val_decl  in
                      match uu____11452 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____11391 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____11488,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____11490;
                           FStar_Syntax_Syntax.lbtyp = uu____11491;
                           FStar_Syntax_Syntax.lbeff = uu____11492;
                           FStar_Syntax_Syntax.lbdef = uu____11493;
                           FStar_Syntax_Syntax.lbattrs = uu____11494;
                           FStar_Syntax_Syntax.lbpos = uu____11495;_}::[]),uu____11496)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____11515 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____11515 with
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
                  let uu____11553 =
                    let uu____11556 =
                      let uu____11557 =
                        let uu____11565 =
                          let uu____11566 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____11567 =
                            let uu____11578 =
                              let uu____11579 =
                                let uu____11584 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____11584)  in
                              FStar_SMTEncoding_Util.mkEq uu____11579  in
                            ([[b2t_x]], [xx], uu____11578)  in
                          FStar_SMTEncoding_Term.mkForall uu____11566
                            uu____11567
                           in
                        (uu____11565,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____11557  in
                    [uu____11556]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____11553
                   in
                (decls, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____11622,uu____11623) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___385_11633  ->
                   match uu___385_11633 with
                   | FStar_Syntax_Syntax.Discriminator uu____11635 -> true
                   | uu____11637 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____11639,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____11651 =
                      let uu____11653 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____11653.FStar_Ident.idText  in
                    uu____11651 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___386_11660  ->
                      match uu___386_11660 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____11663 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11666) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___387_11680  ->
                   match uu___387_11680 with
                   | FStar_Syntax_Syntax.Projector uu____11682 -> true
                   | uu____11688 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____11692 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____11692 with
            | FStar_Pervasives_Native.Some uu____11699 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___404_11701 = se  in
                  let uu____11702 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____11702;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___404_11701.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___404_11701.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___404_11701.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11705) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11720) ->
           let uu____11729 = encode_sigelts env ses  in
           (match uu____11729 with
            | (g,env1) ->
                let uu____11746 =
                  FStar_All.pipe_right g
                    (FStar_List.partition
                       (fun uu___388_11769  ->
                          match uu___388_11769 with
                          | FStar_SMTEncoding_Term.Assume
                              {
                                FStar_SMTEncoding_Term.assumption_term =
                                  uu____11771;
                                FStar_SMTEncoding_Term.assumption_caption =
                                  FStar_Pervasives_Native.Some
                                  "inversion axiom";
                                FStar_SMTEncoding_Term.assumption_name =
                                  uu____11772;
                                FStar_SMTEncoding_Term.assumption_fact_ids =
                                  uu____11773;_}
                              -> false
                          | uu____11780 -> true))
                   in
                (match uu____11746 with
                 | (g',inversions) ->
                     let uu____11796 =
                       FStar_All.pipe_right g'
                         (FStar_List.partition
                            (fun uu___389_11817  ->
                               match uu___389_11817 with
                               | FStar_SMTEncoding_Term.DeclFun uu____11819
                                   -> true
                               | uu____11832 -> false))
                        in
                     (match uu____11796 with
                      | (decls,rest) ->
                          ((FStar_List.append decls
                              (FStar_List.append rest inversions)), env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____11852,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____11865 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____11865 with
             | (usubst,uvs) ->
                 let uu____11885 =
                   let uu____11892 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____11893 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____11894 =
                     let uu____11895 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____11895 k  in
                   (uu____11892, uu____11893, uu____11894)  in
                 (match uu____11885 with
                  | (env1,tps1,k1) ->
                      let uu____11908 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____11908 with
                       | (tps2,k2) ->
                           let uu____11916 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____11916 with
                            | (uu____11932,k3) ->
                                let uu____11954 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____11954 with
                                 | (tps3,env_tps,uu____11966,us) ->
                                     let u_k =
                                       let uu____11969 =
                                         let uu____11970 =
                                           FStar_Syntax_Subst.compress k3  in
                                         uu____11970.FStar_Syntax_Syntax.n
                                          in
                                       match uu____11969 with
                                       | FStar_Syntax_Syntax.Tm_type u -> u
                                       | FStar_Syntax_Syntax.Tm_fvar fv when
                                           FStar_Syntax_Syntax.fv_eq_lid fv
                                             FStar_Parser_Const.eqtype_lid
                                           -> FStar_Syntax_Syntax.U_zero
                                       | uu____11975 ->
                                           let uu____11976 =
                                             let uu____11978 =
                                               FStar_Syntax_Print.term_to_string
                                                 k3
                                                in
                                             FStar_Util.format1
                                               "Impossible: Type of inductive is %s"
                                               uu____11978
                                              in
                                           failwith uu____11976
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____11994) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____12000,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____12003) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____12011,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | uu____12018 -> false  in
                                     let u_leq_u_k u =
                                       let uu____12031 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____12031 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____12049 = u_leq_u_k u_tp  in
                                       if uu____12049
                                       then true
                                       else
                                         (let uu____12056 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____12056 with
                                          | (formals,uu____12073) ->
                                              let uu____12094 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____12094 with
                                               | (uu____12104,uu____12105,uu____12106,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____12117 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____12117
             then
               let uu____12122 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____12122
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___390_12142  ->
                       match uu___390_12142 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____12146 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____12159 = c  in
                 match uu____12159 with
                 | (name,args,uu____12164,uu____12165,uu____12166) ->
                     let uu____12177 =
                       let uu____12178 =
                         let uu____12190 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____12217  ->
                                   match uu____12217 with
                                   | (uu____12226,sort,uu____12228) -> sort))
                            in
                         (name, uu____12190,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____12178  in
                     [uu____12177]
               else
                 (let uu____12239 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____12239 c)
                in
             let inversion_axioms tapp vars =
               let uu____12257 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____12265 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____12265 FStar_Option.isNone))
                  in
               if uu____12257
               then []
               else
                 (let uu____12300 =
                    FStar_SMTEncoding_Env.fresh_fvar "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____12300 with
                  | (xxsym,xx) ->
                      let uu____12313 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____12352  ->
                                fun l  ->
                                  match uu____12352 with
                                  | (out,decls) ->
                                      let uu____12372 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____12372 with
                                       | (uu____12383,data_t) ->
                                           let uu____12385 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____12385 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____12429 =
                                                    let uu____12430 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____12430.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____12429 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____12433,indices)
                                                      -> indices
                                                  | uu____12459 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____12489  ->
                                                            match uu____12489
                                                            with
                                                            | (x,uu____12497)
                                                                ->
                                                                let uu____12502
                                                                  =
                                                                  let uu____12503
                                                                    =
                                                                    let uu____12511
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____12511,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____12503
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____12502)
                                                       env)
                                                   in
                                                let uu____12516 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____12516 with
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
                                                                  let uu____12551
                                                                    =
                                                                    let uu____12556
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____12556,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____12551)
                                                             vars indices1
                                                         else []  in
                                                       let uu____12559 =
                                                         let uu____12560 =
                                                           let uu____12565 =
                                                             let uu____12566
                                                               =
                                                               let uu____12571
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____12572
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____12571,
                                                                 uu____12572)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____12566
                                                              in
                                                           (out, uu____12565)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____12560
                                                          in
                                                       (uu____12559,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____12313 with
                       | (data_ax,decls) ->
                           let uu____12587 =
                             FStar_SMTEncoding_Env.fresh_fvar "f"
                               FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____12587 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____12604 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____12604 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____12611 =
                                    let uu____12619 =
                                      let uu____12620 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____12621 =
                                        let uu____12632 =
                                          let uu____12633 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____12635 =
                                            let uu____12638 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____12638 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____12633 uu____12635
                                           in
                                        let uu____12640 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____12632,
                                          uu____12640)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____12620 uu____12621
                                       in
                                    let uu____12649 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.strcat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____12619,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____12649)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____12611
                                   in
                                FStar_List.append decls
                                  [fuel_guarded_inversion])))
                in
             let uu____12655 =
               let uu____12660 =
                 let uu____12661 = FStar_Syntax_Subst.compress k  in
                 uu____12661.FStar_Syntax_Syntax.n  in
               match uu____12660 with
               | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                   ((FStar_List.append tps formals),
                     (FStar_Syntax_Util.comp_result kres))
               | uu____12696 -> (tps, k)  in
             match uu____12655 with
             | (formals,res) ->
                 let uu____12703 = FStar_Syntax_Subst.open_term formals res
                    in
                 (match uu____12703 with
                  | (formals1,res1) ->
                      let uu____12714 =
                        FStar_SMTEncoding_EncodeTerm.encode_binders
                          FStar_Pervasives_Native.None formals1 env
                         in
                      (match uu____12714 with
                       | (vars,guards,env',binder_decls,uu____12739) ->
                           let arity = FStar_List.length vars  in
                           let uu____12753 =
                             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                               env t arity
                              in
                           (match uu____12753 with
                            | (tname,ttok,env1) ->
                                let ttok_tm =
                                  FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                                let guard =
                                  FStar_SMTEncoding_Util.mk_and_l guards  in
                                let tapp =
                                  let uu____12783 =
                                    let uu____12791 =
                                      FStar_List.map
                                        FStar_SMTEncoding_Util.mkFreeV vars
                                       in
                                    (tname, uu____12791)  in
                                  FStar_SMTEncoding_Util.mkApp uu____12783
                                   in
                                let uu____12797 =
                                  let tname_decl =
                                    let uu____12807 =
                                      let uu____12808 =
                                        FStar_All.pipe_right vars
                                          (FStar_List.map
                                             (fun fv  ->
                                                let uu____12827 =
                                                  let uu____12829 =
                                                    FStar_SMTEncoding_Term.fv_name
                                                      fv
                                                     in
                                                  Prims.strcat tname
                                                    uu____12829
                                                   in
                                                let uu____12831 =
                                                  FStar_SMTEncoding_Term.fv_sort
                                                    fv
                                                   in
                                                (uu____12827, uu____12831,
                                                  false)))
                                         in
                                      let uu____12835 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                          ()
                                         in
                                      (tname, uu____12808,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        uu____12835, false)
                                       in
                                    constructor_or_logic_type_decl
                                      uu____12807
                                     in
                                  let uu____12843 =
                                    match vars with
                                    | [] ->
                                        let uu____12856 =
                                          let uu____12857 =
                                            let uu____12860 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (tname, [])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_3  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_3) uu____12860
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env1 t arity tname uu____12857
                                           in
                                        ([], uu____12856)
                                    | uu____12872 ->
                                        let ttok_decl =
                                          FStar_SMTEncoding_Term.DeclFun
                                            (ttok, [],
                                              FStar_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "token"))
                                           in
                                        let ttok_fresh =
                                          let uu____12882 =
                                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                              ()
                                             in
                                          FStar_SMTEncoding_Term.fresh_token
                                            (ttok,
                                              FStar_SMTEncoding_Term.Term_sort)
                                            uu____12882
                                           in
                                        let ttok_app =
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ttok_tm vars
                                           in
                                        let pats = [[ttok_app]; [tapp]]  in
                                        let name_tok_corr =
                                          let uu____12898 =
                                            let uu____12906 =
                                              let uu____12907 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              let uu____12908 =
                                                let uu____12924 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats,
                                                  FStar_Pervasives_Native.None,
                                                  vars, uu____12924)
                                                 in
                                              FStar_SMTEncoding_Term.mkForall'
                                                uu____12907 uu____12908
                                               in
                                            (uu____12906,
                                              (FStar_Pervasives_Native.Some
                                                 "name-token correspondence"),
                                              (Prims.strcat
                                                 "token_correspondence_" ttok))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____12898
                                           in
                                        ([ttok_decl;
                                         ttok_fresh;
                                         name_tok_corr], env1)
                                     in
                                  match uu____12843 with
                                  | (tok_decls,env2) ->
                                      let uu____12951 =
                                        FStar_Ident.lid_equals t
                                          FStar_Parser_Const.lex_t_lid
                                         in
                                      if uu____12951
                                      then (tok_decls, env2)
                                      else
                                        ((FStar_List.append tname_decl
                                            tok_decls), env2)
                                   in
                                (match uu____12797 with
                                 | (decls,env2) ->
                                     let kindingAx =
                                       let uu____12979 =
                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                           FStar_Pervasives_Native.None res1
                                           env' tapp
                                          in
                                       match uu____12979 with
                                       | (k1,decls1) ->
                                           let karr =
                                             if
                                               (FStar_List.length formals1) >
                                                 (Prims.parse_int "0")
                                             then
                                               let uu____13001 =
                                                 let uu____13002 =
                                                   let uu____13010 =
                                                     let uu____13011 =
                                                       FStar_SMTEncoding_Term.mk_PreType
                                                         ttok_tm
                                                        in
                                                     FStar_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu____13011
                                                      in
                                                   (uu____13010,
                                                     (FStar_Pervasives_Native.Some
                                                        "kinding"),
                                                     (Prims.strcat
                                                        "pre_kinding_" ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____13002
                                                  in
                                               [uu____13001]
                                             else []  in
                                           let uu____13019 =
                                             let uu____13022 =
                                               let uu____13025 =
                                                 let uu____13026 =
                                                   let uu____13034 =
                                                     let uu____13035 =
                                                       FStar_Ident.range_of_lid
                                                         t
                                                        in
                                                     let uu____13036 =
                                                       let uu____13047 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k1)
                                                          in
                                                       ([[tapp]], vars,
                                                         uu____13047)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____13035
                                                       uu____13036
                                                      in
                                                   (uu____13034,
                                                     FStar_Pervasives_Native.None,
                                                     (Prims.strcat "kinding_"
                                                        ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____13026
                                                  in
                                               [uu____13025]  in
                                             FStar_List.append karr
                                               uu____13022
                                              in
                                           FStar_List.append decls1
                                             uu____13019
                                        in
                                     let aux =
                                       let uu____13062 =
                                         let uu____13065 =
                                           inversion_axioms tapp vars  in
                                         let uu____13068 =
                                           let uu____13071 =
                                             let uu____13072 =
                                               FStar_Ident.range_of_lid t  in
                                             pretype_axiom uu____13072 env2
                                               tapp vars
                                              in
                                           [uu____13071]  in
                                         FStar_List.append uu____13065
                                           uu____13068
                                          in
                                       FStar_List.append kindingAx
                                         uu____13062
                                        in
                                     let g =
                                       FStar_List.append decls
                                         (FStar_List.append binder_decls aux)
                                        in
                                     (g, env2)))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____13077,uu____13078,uu____13079,uu____13080,uu____13081)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____13089,t,uu____13091,n_tps,uu____13093) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____13103 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____13103 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____13151 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____13151 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____13179 =
                       FStar_SMTEncoding_Env.fresh_fvar "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____13179 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____13199 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____13199 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____13278 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____13278,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____13285 =
                                   let uu____13286 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____13286, true)
                                    in
                                 let uu____13294 =
                                   let uu____13301 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____13301
                                    in
                                 FStar_All.pipe_right uu____13285 uu____13294
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
                               let uu____13313 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____13313 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____13325::uu____13326 ->
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
                                            let uu____13375 =
                                              let uu____13376 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____13376]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____13375
                                             in
                                          let uu____13402 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____13403 =
                                            let uu____13414 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____13414)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____13402 uu____13403
                                      | uu____13441 -> tok_typing  in
                                    let uu____13452 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____13452 with
                                     | (vars',guards',env'',decls_formals,uu____13477)
                                         ->
                                         let uu____13490 =
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
                                         (match uu____13490 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____13520 ->
                                                    let uu____13529 =
                                                      let uu____13530 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____13530
                                                       in
                                                    [uu____13529]
                                                 in
                                              let encode_elim uu____13546 =
                                                let uu____13547 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____13547 with
                                                | (head1,args) ->
                                                    let uu____13598 =
                                                      let uu____13599 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____13599.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____13598 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13611;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13612;_},uu____13613)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____13619 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____13619
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
                                                                  | uu____13682
                                                                    ->
                                                                    let uu____13683
                                                                    =
                                                                    let uu____13689
                                                                    =
                                                                    let uu____13691
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13691
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13689)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13683
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13714
                                                                    =
                                                                    let uu____13716
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13716
                                                                     in
                                                                    if
                                                                    uu____13714
                                                                    then
                                                                    let uu____13738
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13738]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____13741
                                                                =
                                                                let uu____13755
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____13812
                                                                     ->
                                                                    fun
                                                                    uu____13813
                                                                     ->
                                                                    match 
                                                                    (uu____13812,
                                                                    uu____13813)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13924
                                                                    =
                                                                    let uu____13932
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13932
                                                                     in
                                                                    (match uu____13924
                                                                    with
                                                                    | 
                                                                    (uu____13946,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13957
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13957
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13962
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
                                                                  uu____13755
                                                                 in
                                                              (match uu____13741
                                                               with
                                                               | (uu____13983,arg_vars,elim_eqns_or_guards,uu____13986)
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
                                                                    let uu____14013
                                                                    =
                                                                    let uu____14021
                                                                    =
                                                                    let uu____14022
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14023
                                                                    =
                                                                    let uu____14034
                                                                    =
                                                                    let uu____14035
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14035
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14037
                                                                    =
                                                                    let uu____14038
                                                                    =
                                                                    let uu____14043
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14043)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14038
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14034,
                                                                    uu____14037)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14022
                                                                    uu____14023
                                                                     in
                                                                    (uu____14021,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14013
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14058
                                                                    =
                                                                    let uu____14059
                                                                    =
                                                                    let uu____14065
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14065,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14059
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14058
                                                                     in
                                                                    let uu____14068
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14068
                                                                    then
                                                                    let x =
                                                                    let uu____14072
                                                                    =
                                                                    let uu____14078
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14078,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14072
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14083
                                                                    =
                                                                    let uu____14091
                                                                    =
                                                                    let uu____14092
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14093
                                                                    =
                                                                    let uu____14104
                                                                    =
                                                                    let uu____14109
                                                                    =
                                                                    let uu____14112
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14112]
                                                                     in
                                                                    [uu____14109]
                                                                     in
                                                                    let uu____14117
                                                                    =
                                                                    let uu____14118
                                                                    =
                                                                    let uu____14123
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14125
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14123,
                                                                    uu____14125)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14118
                                                                     in
                                                                    (uu____14104,
                                                                    [x],
                                                                    uu____14117)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14092
                                                                    uu____14093
                                                                     in
                                                                    let uu____14146
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14091,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14146)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14083
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14157
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
                                                                    (let uu____14180
                                                                    =
                                                                    let uu____14181
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14181
                                                                    dapp1  in
                                                                    [uu____14180])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14157
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14188
                                                                    =
                                                                    let uu____14196
                                                                    =
                                                                    let uu____14197
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14198
                                                                    =
                                                                    let uu____14209
                                                                    =
                                                                    let uu____14210
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14210
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14212
                                                                    =
                                                                    let uu____14213
                                                                    =
                                                                    let uu____14218
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14218)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14213
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14209,
                                                                    uu____14212)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14197
                                                                    uu____14198
                                                                     in
                                                                    (uu____14196,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14188)
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
                                                         let uu____14237 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____14237
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
                                                                  | uu____14300
                                                                    ->
                                                                    let uu____14301
                                                                    =
                                                                    let uu____14307
                                                                    =
                                                                    let uu____14309
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14309
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14307)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14301
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14332
                                                                    =
                                                                    let uu____14334
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14334
                                                                     in
                                                                    if
                                                                    uu____14332
                                                                    then
                                                                    let uu____14356
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14356]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14359
                                                                =
                                                                let uu____14373
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14430
                                                                     ->
                                                                    fun
                                                                    uu____14431
                                                                     ->
                                                                    match 
                                                                    (uu____14430,
                                                                    uu____14431)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14542
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14550
                                                                     in
                                                                    (match uu____14542
                                                                    with
                                                                    | 
                                                                    (uu____14564,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14575
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14575
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14580
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14580
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
                                                                  uu____14373
                                                                 in
                                                              (match uu____14359
                                                               with
                                                               | (uu____14601,arg_vars,elim_eqns_or_guards,uu____14604)
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
                                                                    let uu____14631
                                                                    =
                                                                    let uu____14639
                                                                    =
                                                                    let uu____14640
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14652
                                                                    =
                                                                    let uu____14653
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14653
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14655
                                                                    =
                                                                    let uu____14656
                                                                    =
                                                                    let uu____14661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14661)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14656
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14652,
                                                                    uu____14655)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14640
                                                                    uu____14641
                                                                     in
                                                                    (uu____14639,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14631
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14676
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    let uu____14683
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14683,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14677
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14676
                                                                     in
                                                                    let uu____14686
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14686
                                                                    then
                                                                    let x =
                                                                    let uu____14690
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14696,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14690
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14701
                                                                    =
                                                                    let uu____14709
                                                                    =
                                                                    let uu____14710
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14711
                                                                    =
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14730
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14730]
                                                                     in
                                                                    [uu____14727]
                                                                     in
                                                                    let uu____14735
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    let uu____14741
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14743
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14741,
                                                                    uu____14743)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14736
                                                                     in
                                                                    (uu____14722,
                                                                    [x],
                                                                    uu____14735)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14710
                                                                    uu____14711
                                                                     in
                                                                    let uu____14764
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14709,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14764)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14701
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14775
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
                                                                    (let uu____14798
                                                                    =
                                                                    let uu____14799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14799
                                                                    dapp1  in
                                                                    [uu____14798])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14775
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14814
                                                                    =
                                                                    let uu____14815
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14816
                                                                    =
                                                                    let uu____14827
                                                                    =
                                                                    let uu____14828
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14828
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14830
                                                                    =
                                                                    let uu____14831
                                                                    =
                                                                    let uu____14836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14836)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14831
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14827,
                                                                    uu____14830)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14815
                                                                    uu____14816
                                                                     in
                                                                    (uu____14814,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14806)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____14853 ->
                                                         ((let uu____14855 =
                                                             let uu____14861
                                                               =
                                                               let uu____14863
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____14865
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____14863
                                                                 uu____14865
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____14861)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____14855);
                                                          ([], [])))
                                                 in
                                              let uu____14873 =
                                                encode_elim ()  in
                                              (match uu____14873 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____14899 =
                                                       let uu____14902 =
                                                         let uu____14905 =
                                                           let uu____14908 =
                                                             let uu____14911
                                                               =
                                                               let uu____14912
                                                                 =
                                                                 let uu____14924
                                                                   =
                                                                   let uu____14925
                                                                    =
                                                                    let uu____14927
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14927
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____14925
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   uu____14924)
                                                                  in
                                                               FStar_SMTEncoding_Term.DeclFun
                                                                 uu____14912
                                                                in
                                                             [uu____14911]
                                                              in
                                                           let uu____14934 =
                                                             let uu____14937
                                                               =
                                                               let uu____14940
                                                                 =
                                                                 let uu____14943
                                                                   =
                                                                   let uu____14946
                                                                    =
                                                                    let uu____14949
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14954
                                                                    =
                                                                    let uu____14957
                                                                    =
                                                                    let uu____14958
                                                                    =
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14967
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14968
                                                                    =
                                                                    let uu____14979
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14979)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14967
                                                                    uu____14968
                                                                     in
                                                                    (uu____14966,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14958
                                                                     in
                                                                    let uu____14992
                                                                    =
                                                                    let uu____14995
                                                                    =
                                                                    let uu____14996
                                                                    =
                                                                    let uu____15004
                                                                    =
                                                                    let uu____15005
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15006
                                                                    =
                                                                    let uu____15017
                                                                    =
                                                                    let uu____15018
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15018
                                                                    vars'  in
                                                                    let uu____15020
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15017,
                                                                    uu____15020)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15005
                                                                    uu____15006
                                                                     in
                                                                    (uu____15004,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14996
                                                                     in
                                                                    [uu____14995]
                                                                     in
                                                                    uu____14957
                                                                    ::
                                                                    uu____14992
                                                                     in
                                                                    uu____14949
                                                                    ::
                                                                    uu____14954
                                                                     in
                                                                   FStar_List.append
                                                                    uu____14946
                                                                    elim
                                                                    in
                                                                 FStar_List.append
                                                                   decls_pred
                                                                   uu____14943
                                                                  in
                                                               FStar_List.append
                                                                 decls_formals
                                                                 uu____14940
                                                                in
                                                             FStar_List.append
                                                               proxy_fresh
                                                               uu____14937
                                                              in
                                                           FStar_List.append
                                                             uu____14908
                                                             uu____14934
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____14905
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____14902
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____14899
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
           (fun uu____15058  ->
              fun se  ->
                match uu____15058 with
                | (g,env1) ->
                    let uu____15078 = encode_sigelt env1 se  in
                    (match uu____15078 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15146 =
        match uu____15146 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15183 ->
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
                 ((let uu____15191 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15191
                   then
                     let uu____15196 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15198 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15200 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15196 uu____15198 uu____15200
                   else ());
                  (let uu____15205 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15205 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15223 =
                         let uu____15231 =
                           let uu____15233 =
                             let uu____15235 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15235
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15233  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15231
                          in
                       (match uu____15223 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15255 = FStar_Options.log_queries ()
                                 in
                              if uu____15255
                              then
                                let uu____15258 =
                                  let uu____15260 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15262 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15264 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15260 uu____15262 uu____15264
                                   in
                                FStar_Pervasives_Native.Some uu____15258
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15288,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15308 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15308 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15335 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15335 with | (uu____15362,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15415  ->
              match uu____15415 with
              | (l,uu____15424,uu____15425) ->
                  let uu____15428 =
                    let uu____15440 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____15440, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____15428))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15473  ->
              match uu____15473 with
              | (l,uu____15484,uu____15485) ->
                  let uu____15488 =
                    let uu____15489 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____15489
                     in
                  let uu____15492 =
                    let uu____15495 =
                      let uu____15496 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15496  in
                    [uu____15495]  in
                  uu____15488 :: uu____15492))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15525 =
      let uu____15528 =
        let uu____15529 = FStar_Util.psmap_empty ()  in
        let uu____15544 = FStar_Util.psmap_empty ()  in
        let uu____15547 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15551 =
          let uu____15553 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15553 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15529;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15544;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____15547;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15551;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____15528]  in
    FStar_ST.op_Colon_Equals last_env uu____15525
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15595 = FStar_ST.op_Bang last_env  in
      match uu____15595 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15623 ->
          let uu___405_15626 = e  in
          let uu____15627 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___405_15626.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___405_15626.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___405_15626.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___405_15626.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___405_15626.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___405_15626.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___405_15626.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___405_15626.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15627;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___405_15626.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15635 = FStar_ST.op_Bang last_env  in
    match uu____15635 with
    | [] -> failwith "Empty env stack"
    | uu____15662::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15694  ->
    let uu____15695 = FStar_ST.op_Bang last_env  in
    match uu____15695 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15755  ->
    let uu____15756 = FStar_ST.op_Bang last_env  in
    match uu____15756 with
    | [] -> failwith "Popping an empty stack"
    | uu____15783::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15820  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15873  ->
         let uu____15874 = snapshot_env ()  in
         match uu____15874 with
         | (env_depth,()) ->
             let uu____15896 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____15896 with
              | (varops_depth,()) ->
                  let uu____15918 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____15918 with
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
        (fun uu____15976  ->
           let uu____15977 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____15977 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16072 = snapshot msg  in () 
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
        | (uu____16118::uu____16119,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___406_16127 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___406_16127.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___406_16127.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___406_16127.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16128 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16148 =
        let uu____16151 =
          let uu____16152 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16152  in
        let uu____16153 = open_fact_db_tags env  in uu____16151 ::
          uu____16153
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16148
  
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
      let uu____16180 = encode_sigelt env se  in
      match uu____16180 with
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
        let uu____16225 = FStar_Options.log_queries ()  in
        if uu____16225
        then
          let uu____16230 =
            let uu____16231 =
              let uu____16233 =
                let uu____16235 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16235 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16233  in
            FStar_SMTEncoding_Term.Caption uu____16231  in
          uu____16230 :: decls
        else decls  in
      (let uu____16254 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____16254
       then
         let uu____16257 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16257
       else ());
      (let env =
         let uu____16263 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16263 tcenv  in
       let uu____16264 = encode_top_level_facts env se  in
       match uu____16264 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16278 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16278)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16292 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16292
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16307 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____16307
          then
            let uu____16310 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16310
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16356  ->
                    fun se  ->
                      match uu____16356 with
                      | (g,env2) ->
                          let uu____16376 = encode_top_level_facts env2 se
                             in
                          (match uu____16376 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16399 =
            encode_signature
              (let uu___407_16408 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___407_16408.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___407_16408.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___407_16408.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___407_16408.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___407_16408.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___407_16408.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___407_16408.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___407_16408.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___407_16408.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___407_16408.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16399 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____16428 = FStar_Options.log_queries ()  in
                if uu____16428
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
                 (let uu___408_16448 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___408_16448.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___408_16448.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___408_16448.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___408_16448.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___408_16448.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___408_16448.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___408_16448.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___408_16448.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___408_16448.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___408_16448.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____16451 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16451
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
        (let uu____16516 =
           let uu____16518 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16518.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16516);
        (let env =
           let uu____16520 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16520 tcenv  in
         let uu____16521 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16560 = aux rest  in
                 (match uu____16560 with
                  | (out,rest1) ->
                      let t =
                        let uu____16588 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16588 with
                        | FStar_Pervasives_Native.Some uu____16591 ->
                            let uu____16592 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16592
                              x.FStar_Syntax_Syntax.sort
                        | uu____16593 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16597 =
                        let uu____16600 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___409_16603 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___409_16603.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___409_16603.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16600 :: out  in
                      (uu____16597, rest1))
             | uu____16608 -> ([], bindings)  in
           let uu____16615 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16615 with
           | (closing,bindings) ->
               let uu____16642 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16642, bindings)
            in
         match uu____16521 with
         | (q1,bindings) ->
             let uu____16673 = encode_env_bindings env bindings  in
             (match uu____16673 with
              | (env_decls,env1) ->
                  ((let uu____16695 =
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
                    if uu____16695
                    then
                      let uu____16702 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16702
                    else ());
                   (let uu____16707 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16707 with
                    | (phi,qdecls) ->
                        let uu____16728 =
                          let uu____16733 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16733 phi
                           in
                        (match uu____16728 with
                         | (labels,phi1) ->
                             let uu____16750 = encode_labels labels  in
                             (match uu____16750 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____16786 =
                                      FStar_Options.log_queries ()  in
                                    if uu____16786
                                    then
                                      let uu____16791 =
                                        let uu____16792 =
                                          let uu____16794 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____16794
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____16792
                                         in
                                      [uu____16791]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____16803 =
                                      let uu____16811 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16812 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____16811,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16812)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16803
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
  