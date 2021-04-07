open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] in
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStar_TypeChecker_Env.current_module
              env.FStar_SMTEncoding_Env.tcenv in
          FStar_Ident.string_of_lid uu___2 in
        FStar_Pervasives_Native.Some uu___1 in
      FStar_Profiling.profile
        (fun uu___1 ->
           FStar_TypeChecker_Normalize.normalize steps
             env.FStar_SMTEncoding_Env.tcenv t) uu___
        "FStar.SMTEncoding.Encode.norm_before_encoding"
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 -> FStar_TypeChecker_Normalize.normalize steps env t)
          uu___ "FStar.SMTEncoding.Encode.norm"
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
  = fun projectee -> match projectee with | { mk; is;_} -> mk
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee -> match projectee with | { mk; is;_} -> is
let (prims : prims_t) =
  let module_name = "Prims" in
  let uu___ =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort in
  match uu___ with
  | (asym, a) ->
      let uu___1 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort in
      (match uu___1 with
       | (xsym, x) ->
           let uu___2 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort in
           (match uu___2 with
            | (ysym, y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu___3 =
                      let uu___4 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort) in
                      (x1, uu___4, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu___3 in
                  let xtok = Prims.op_Hat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu___3 =
                      let uu___4 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu___4) in
                    FStar_SMTEncoding_Util.mkApp uu___3 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars in
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_All.pipe_right (FStar_Util.prefix vars)
                        FStar_Pervasives_Native.fst in
                    let axiom_name = Prims.op_Hat "primitive_tot_fun_" x1 in
                    let tot_fun_axiom_for_x =
                      let uu___3 =
                        let uu___4 = FStar_SMTEncoding_Term.mk_IsTotFun xtok1 in
                        (uu___4, FStar_Pervasives_Native.None, axiom_name) in
                      FStar_SMTEncoding_Util.mkAssume uu___3 in
                    let uu___3 =
                      FStar_List.fold_left
                        (fun uu___4 ->
                           fun var ->
                             match uu___4 with
                             | (axioms, app, vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var] in
                                 let vars2 = FStar_List.append vars1 [var] in
                                 let axiom_name1 =
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length in
                                       Prims.string_of_int uu___7 in
                                     Prims.op_Hat "." uu___6 in
                                   Prims.op_Hat axiom_name uu___5 in
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1 in
                                             ([[app1]], vars2, uu___11) in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu___10 in
                                         (uu___9,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1) in
                                       FStar_SMTEncoding_Util.mkAssume uu___8 in
                                     [uu___7] in
                                   FStar_List.append axioms uu___6 in
                                 (uu___5, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one in
                    match uu___3 with | (axioms, uu___4, uu___5) -> axioms in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                  ([[xapp]], vars, uu___11) in
                                FStar_SMTEncoding_Term.mkForall rng uu___10 in
                              (uu___9, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu___8 in
                          [uu___7] in
                        xtok_decl :: uu___6 in
                      xname_decl :: uu___5 in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp) in
                                ([[xtok_app]], vars, uu___11) in
                              FStar_SMTEncoding_Term.mkForall rng uu___10 in
                            (uu___9,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu___8 in
                        [uu___7] in
                      FStar_List.append tot_fun_axioms uu___6 in
                    FStar_List.append uu___4 uu___5 in
                  (xtok1, (FStar_List.length vars), uu___3) in
                let axy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(asym, FStar_SMTEncoding_Term.Term_sort);
                    (xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu___6 in
                      quant axy uu___5 in
                    (FStar_Parser_Const.op_Eq, uu___4) in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu___9 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu___8 in
                        quant axy uu___7 in
                      (FStar_Parser_Const.op_notEq, uu___6) in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  FStar_SMTEncoding_Term.unboxBool x in
                                let uu___13 =
                                  FStar_SMTEncoding_Term.unboxBool y in
                                (uu___12, uu___13) in
                              FStar_SMTEncoding_Util.mkAnd uu___11 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu___10 in
                          quant xy uu___9 in
                        (FStar_Parser_Const.op_And, uu___8) in
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              let uu___12 =
                                let uu___13 =
                                  let uu___14 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  let uu___15 =
                                    FStar_SMTEncoding_Term.unboxBool y in
                                  (uu___14, uu___15) in
                                FStar_SMTEncoding_Util.mkOr uu___13 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu___12 in
                            quant xy uu___11 in
                          (FStar_Parser_Const.op_Or, uu___10) in
                        let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                let uu___14 =
                                  let uu___15 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  FStar_SMTEncoding_Util.mkNot uu___15 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu___14 in
                              quant qx uu___13 in
                            (FStar_Parser_Const.op_Negation, uu___12) in
                          let uu___12 =
                            let uu___13 =
                              let uu___14 =
                                let uu___15 =
                                  let uu___16 =
                                    let uu___17 =
                                      let uu___18 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu___19 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu___18, uu___19) in
                                    FStar_SMTEncoding_Util.mkLT uu___17 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu___16 in
                                quant xy uu___15 in
                              (FStar_Parser_Const.op_LT, uu___14) in
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 =
                                    let uu___18 =
                                      let uu___19 =
                                        let uu___20 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu___21 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu___20, uu___21) in
                                      FStar_SMTEncoding_Util.mkLTE uu___19 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool uu___18 in
                                  quant xy uu___17 in
                                (FStar_Parser_Const.op_LTE, uu___16) in
                              let uu___16 =
                                let uu___17 =
                                  let uu___18 =
                                    let uu___19 =
                                      let uu___20 =
                                        let uu___21 =
                                          let uu___22 =
                                            FStar_SMTEncoding_Term.unboxInt x in
                                          let uu___23 =
                                            FStar_SMTEncoding_Term.unboxInt y in
                                          (uu___22, uu___23) in
                                        FStar_SMTEncoding_Util.mkGT uu___21 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu___20 in
                                    quant xy uu___19 in
                                  (FStar_Parser_Const.op_GT, uu___18) in
                                let uu___18 =
                                  let uu___19 =
                                    let uu___20 =
                                      let uu___21 =
                                        let uu___22 =
                                          let uu___23 =
                                            let uu___24 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu___25 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu___24, uu___25) in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu___23 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu___22 in
                                      quant xy uu___21 in
                                    (FStar_Parser_Const.op_GTE, uu___20) in
                                  let uu___20 =
                                    let uu___21 =
                                      let uu___22 =
                                        let uu___23 =
                                          let uu___24 =
                                            let uu___25 =
                                              let uu___26 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu___27 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu___26, uu___27) in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu___25 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu___24 in
                                        quant xy uu___23 in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu___22) in
                                    let uu___22 =
                                      let uu___23 =
                                        let uu___24 =
                                          let uu___25 =
                                            let uu___26 =
                                              let uu___27 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu___27 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu___26 in
                                          quant qx uu___25 in
                                        (FStar_Parser_Const.op_Minus,
                                          uu___24) in
                                      let uu___24 =
                                        let uu___25 =
                                          let uu___26 =
                                            let uu___27 =
                                              let uu___28 =
                                                let uu___29 =
                                                  let uu___30 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu___31 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu___30, uu___31) in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu___29 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu___28 in
                                            quant xy uu___27 in
                                          (FStar_Parser_Const.op_Addition,
                                            uu___26) in
                                        let uu___26 =
                                          let uu___27 =
                                            let uu___28 =
                                              let uu___29 =
                                                let uu___30 =
                                                  let uu___31 =
                                                    let uu___32 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x in
                                                    let uu___33 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y in
                                                    (uu___32, uu___33) in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu___31 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu___30 in
                                              quant xy uu___29 in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu___28) in
                                          let uu___28 =
                                            let uu___29 =
                                              let uu___30 =
                                                let uu___31 =
                                                  let uu___32 =
                                                    let uu___33 =
                                                      let uu___34 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x in
                                                      let uu___35 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y in
                                                      (uu___34, uu___35) in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu___33 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu___32 in
                                                quant xy uu___31 in
                                              (FStar_Parser_Const.op_Division,
                                                uu___30) in
                                            let uu___30 =
                                              let uu___31 =
                                                let uu___32 =
                                                  let uu___33 =
                                                    let uu___34 =
                                                      let uu___35 =
                                                        let uu___36 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x in
                                                        let uu___37 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y in
                                                        (uu___36, uu___37) in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu___35 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu___34 in
                                                  quant xy uu___33 in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu___32) in
                                              let uu___32 =
                                                let uu___33 =
                                                  let uu___34 =
                                                    let uu___35 =
                                                      let uu___36 =
                                                        let uu___37 =
                                                          let uu___38 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x in
                                                          let uu___39 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y in
                                                          (uu___38, uu___39) in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu___37 in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu___36 in
                                                    quant xy uu___35 in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu___34) in
                                                let uu___34 =
                                                  let uu___35 =
                                                    let uu___36 =
                                                      let uu___37 =
                                                        let uu___38 =
                                                          let uu___39 =
                                                            let uu___40 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x in
                                                            let uu___41 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y in
                                                            (uu___40,
                                                              uu___41) in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu___39 in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu___38 in
                                                      quant xy uu___37 in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu___36) in
                                                  let uu___36 =
                                                    let uu___37 =
                                                      let uu___38 =
                                                        let uu___39 =
                                                          let uu___40 =
                                                            let uu___41 =
                                                              let uu___42 =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x in
                                                              let uu___43 =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y in
                                                              (uu___42,
                                                                uu___43) in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu___41 in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu___40 in
                                                        quant xy uu___39 in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu___38) in
                                                    let uu___38 =
                                                      let uu___39 =
                                                        let uu___40 =
                                                          let uu___41 =
                                                            let uu___42 =
                                                              let uu___43 =
                                                                let uu___44 =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                let uu___45 =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                (uu___44,
                                                                  uu___45) in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu___43 in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu___42 in
                                                          quant xy uu___41 in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu___40) in
                                                      let uu___40 =
                                                        let uu___41 =
                                                          let uu___42 =
                                                            let uu___43 =
                                                              let uu___44 =
                                                                let uu___45 =
                                                                  let uu___46
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                  let uu___47
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                  (uu___46,
                                                                    uu___47) in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu___45 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu___44 in
                                                            quant xy uu___43 in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu___42) in
                                                        let uu___42 =
                                                          let uu___43 =
                                                            let uu___44 =
                                                              let uu___45 =
                                                                let uu___46 =
                                                                  let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___49
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___48,
                                                                    uu___49) in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu___47 in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu___46 in
                                                              quant xy
                                                                uu___45 in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu___44) in
                                                          let uu___44 =
                                                            let uu___45 =
                                                              let uu___46 =
                                                                let uu___47 =
                                                                  let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___51
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___50,
                                                                    uu___51) in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu___49 in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu___48 in
                                                                quant xy
                                                                  uu___47 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu___46) in
                                                            let uu___46 =
                                                              let uu___47 =
                                                                let uu___48 =
                                                                  let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___53
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___52,
                                                                    uu___53) in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu___51 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu___50 in
                                                                  quant xy
                                                                    uu___49 in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu___48) in
                                                              let uu___48 =
                                                                let uu___49 =
                                                                  let uu___50
                                                                    =
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu___53
                                                                    FStar_Range.dummyRange in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu___52 in
                                                                    quant qx
                                                                    uu___51 in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu___50) in
                                                                [uu___49] in
                                                              uu___47 ::
                                                                uu___48 in
                                                            uu___45 ::
                                                              uu___46 in
                                                          uu___43 :: uu___44 in
                                                        uu___41 :: uu___42 in
                                                      uu___39 :: uu___40 in
                                                    uu___37 :: uu___38 in
                                                  uu___35 :: uu___36 in
                                                uu___33 :: uu___34 in
                                              uu___31 :: uu___32 in
                                            uu___29 :: uu___30 in
                                          uu___27 :: uu___28 in
                                        uu___25 :: uu___26 in
                                      uu___23 :: uu___24 in
                                    uu___21 :: uu___22 in
                                  uu___19 :: uu___20 in
                                uu___17 :: uu___18 in
                              uu___15 :: uu___16 in
                            uu___13 :: uu___14 in
                          uu___11 :: uu___12 in
                        uu___9 :: uu___10 in
                      uu___7 :: uu___8 in
                    uu___5 :: uu___6 in
                  uu___3 :: uu___4 in
                let mk l v =
                  let uu___3 =
                    let uu___4 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu___5 ->
                              match uu___5 with
                              | (l', uu___6) -> FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu___4
                      (FStar_Option.map
                         (fun uu___5 ->
                            match uu___5 with
                            | (uu___6, b) ->
                                let uu___7 = FStar_Ident.range_of_lid l in
                                b uu___7 v)) in
                  FStar_All.pipe_right uu___3 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu___3 ->
                          match uu___3 with
                          | (l', uu___4) -> FStar_Ident.lid_equals l l')) in
                { mk; is }))
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list
          -> FStar_SMTEncoding_Term.decl)
  =
  fun rng ->
    fun env ->
      fun tapp ->
        fun vars ->
          let uu___ =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort in
          match uu___ with
          | (xxsym, xx) ->
              let uu___1 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort in
              (match uu___1 with
               | (ffsym, ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name in
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort) in
                           let uu___7 =
                             let uu___8 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort) in
                             uu___8 :: vars in
                           uu___6 :: uu___7 in
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx]) in
                                 (tapp, uu___10) in
                               FStar_SMTEncoding_Util.mkEq uu___9 in
                             (xx_has_type, uu___8) in
                           FStar_SMTEncoding_Util.mkImp uu___7 in
                         ([[xx_has_type]], uu___5, uu___6) in
                       FStar_SMTEncoding_Term.mkForall rng uu___4 in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = FStar_Util.digest_of_string tapp_hash in
                           Prims.op_Hat "_pretyping_" uu___7 in
                         Prims.op_Hat module_name uu___6 in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu___5 in
                     (uu___3, (FStar_Pervasives_Native.Some "pretyping"),
                       uu___4) in
                   FStar_SMTEncoding_Util.mkAssume uu___2)
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx =
    FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy =
    FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mkForall_fuel env =
    let uu___ =
      let uu___1 = FStar_TypeChecker_Env.current_module env in
      FStar_Ident.string_of_lid uu___1 in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu___ in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu___2, (FStar_Pervasives_Native.Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu___8) in
                FStar_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStar_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Term.boxBool b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu___8) in
                FStar_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStar_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_int env nm tt =
    let lex_t =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu___2, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu___1 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___ in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu___ =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Term.boxInt b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu___8) in
                FStar_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStar_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 =
                        let uu___12 =
                          let uu___13 =
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu___17 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero in
                                (uu___16, uu___17) in
                              FStar_SMTEncoding_Util.mkGT uu___15 in
                            let uu___15 =
                              let uu___16 =
                                let uu___17 =
                                  let uu___18 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu___19 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero in
                                  (uu___18, uu___19) in
                                FStar_SMTEncoding_Util.mkGTE uu___17 in
                              let uu___17 =
                                let uu___18 =
                                  let uu___19 =
                                    let uu___20 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu___21 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu___20, uu___21) in
                                  FStar_SMTEncoding_Util.mkLT uu___19 in
                                [uu___18] in
                              uu___16 :: uu___17 in
                            uu___14 :: uu___15 in
                          typing_pred_y :: uu___13 in
                        typing_pred :: uu___12 in
                      FStar_SMTEncoding_Util.mk_and_l uu___11 in
                    (uu___10, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu___9 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu___8) in
              let uu___8 =
                let uu___9 = FStar_TypeChecker_Env.get_range env in
                let uu___10 = mkForall_fuel env in uu___10 uu___9 in
              uu___8 uu___7 in
            (uu___6,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu___5 in
        [uu___4] in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let mk_real env nm tt =
    let lex_t =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu___2, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu___1 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___ in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv
        ("a", (FStar_SMTEncoding_Term.Sort "Real")) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv
        ("b", (FStar_SMTEncoding_Term.Sort "Real")) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu___ =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Term.boxReal b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStar_SMTEncoding_Term.boxReal b in
              FStar_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "real typing"), "real_typing") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x in
                  (typing_pred, uu___8) in
                FStar_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStar_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 =
                        let uu___12 =
                          let uu___13 =
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  FStar_SMTEncoding_Term.unboxReal x in
                                let uu___17 =
                                  FStar_SMTEncoding_Util.mkReal "0.0" in
                                (uu___16, uu___17) in
                              FStar_SMTEncoding_Util.mkGT uu___15 in
                            let uu___15 =
                              let uu___16 =
                                let uu___17 =
                                  let uu___18 =
                                    FStar_SMTEncoding_Term.unboxReal y in
                                  let uu___19 =
                                    FStar_SMTEncoding_Util.mkReal "0.0" in
                                  (uu___18, uu___19) in
                                FStar_SMTEncoding_Util.mkGTE uu___17 in
                              let uu___17 =
                                let uu___18 =
                                  let uu___19 =
                                    let uu___20 =
                                      FStar_SMTEncoding_Term.unboxReal y in
                                    let uu___21 =
                                      FStar_SMTEncoding_Term.unboxReal x in
                                    (uu___20, uu___21) in
                                  FStar_SMTEncoding_Util.mkLT uu___19 in
                                [uu___18] in
                              uu___16 :: uu___17 in
                            uu___14 :: uu___15 in
                          typing_pred_y :: uu___13 in
                        typing_pred :: uu___12 in
                      FStar_SMTEncoding_Util.mk_and_l uu___11 in
                    (uu___10, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu___9 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu___8) in
              let uu___8 =
                let uu___9 = FStar_TypeChecker_Env.get_range env in
                let uu___10 = mkForall_fuel env in uu___10 uu___9 in
              uu___8 uu___7 in
            (uu___6,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real") in
          FStar_SMTEncoding_Util.mkAssume uu___5 in
        [uu___4] in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Term.boxString b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu___8) in
                FStar_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStar_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    let uu___ =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp") in
    [uu___] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu___2, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_and_interp env conj uu___ =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStar_TypeChecker_Env.get_range env in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu___8, valid) in
              FStar_SMTEncoding_Util.mkIff uu___7 in
            ([[l_and_a_b]], [aa; bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___4 uu___5 in
        (uu___3, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___2 in
    [uu___1] in
  let mk_or_interp env disj uu___ =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStar_TypeChecker_Env.get_range env in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu___8, valid) in
              FStar_SMTEncoding_Util.mkIff uu___7 in
            ([[l_or_a_b]], [aa; bb], uu___6) in
          FStar_SMTEncoding_Term.mkForall uu___4 uu___5 in
        (uu___3, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___2 in
    [uu___1] in
  let mk_eq2_interp env eq2 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu___7, valid) in
              FStar_SMTEncoding_Util.mkIff uu___6 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_eq3_interp env eq3 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu___7, valid) in
              FStar_SMTEncoding_Util.mkIff uu___6 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_imp_interp env imp tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu___7, valid) in
              FStar_SMTEncoding_Util.mkIff uu___6 in
            ([[l_imp_a_b]], [aa; bb], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_iff_interp env iff tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu___7, valid) in
              FStar_SMTEncoding_Util.mkIff uu___6 in
            ([[l_iff_a_b]], [aa; bb], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu___ = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 = FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu___3 range_ty in
        let uu___3 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const" in
        (uu___2, (FStar_Pervasives_Native.Some "Range_const typing"), uu___3) in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_inversion_axiom env inversion tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu___ = FStar_SMTEncoding_Term.n_fuel Prims.int_one in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu___ x1 t in
      let uu___ = FStar_TypeChecker_Env.get_range env in
      let uu___1 =
        let uu___2 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu___2) in
      FStar_SMTEncoding_Term.mkForall uu___ uu___1 in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu___5) in
          FStar_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_with_type_axiom env with_type tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type, [t; e]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu___8 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu___7, uu___8) in
              FStar_SMTEncoding_Util.mkAnd uu___6 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu___5) in
          FStar_SMTEncoding_Term.mkForall' uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
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
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env ->
    fun t ->
      fun s ->
        fun tt ->
          let uu___ =
            FStar_Util.find_opt
              (fun uu___1 ->
                 match uu___1 with
                 | (l, uu___2) -> FStar_Ident.lid_equals l t) prims1 in
          match uu___ with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (uu___1, f) -> f env s tt
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env ->
    fun fv ->
      fun t ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu___ =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env in
        match uu___ with
        | (form, decls) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = FStar_Ident.string_of_lid lid in
                        Prims.op_Hat "Lemma: " uu___7 in
                      FStar_Pervasives_Native.Some uu___6 in
                    let uu___6 =
                      let uu___7 = FStar_Ident.string_of_lid lid in
                      Prims.op_Hat "lemma_" uu___7 in
                    (form, uu___5, uu___6) in
                  FStar_SMTEncoding_Util.mkAssume uu___4 in
                [uu___3] in
              FStar_All.pipe_right uu___2
                FStar_SMTEncoding_Term.mk_decls_trivial in
            FStar_List.append decls uu___1
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted ->
    fun env ->
      fun fv ->
        fun tt ->
          fun t_norm ->
            fun quals ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu___ =
                ((let uu___1 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu___1) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu___
              then
                let arg_sorts =
                  let uu___1 =
                    let uu___2 = FStar_Syntax_Subst.compress t_norm in
                    uu___2.FStar_Syntax_Syntax.n in
                  match uu___1 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders, uu___2) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu___3 -> FStar_SMTEncoding_Term.Term_sort))
                  | uu___2 -> [] in
                let arity = FStar_List.length arg_sorts in
                let uu___1 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity in
                match uu___1 with
                | (vname, vtok, env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    let uu___2 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial in
                    (uu___2, env1)
              else
                (let uu___2 = prims.is lid in
                 if uu___2
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid in
                   let uu___3 = prims.mk lid vname in
                   match uu___3 with
                   | (tok, arity, definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok) in
                       let uu___4 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial in
                       (uu___4, env1)
                 else
                   (let encode_non_total_function_typ =
                      let uu___4 = FStar_Ident.nsstr lid in uu___4 <> "Prims" in
                    let uu___4 =
                      let uu___5 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm in
                      match uu___5 with
                      | (args, comp) ->
                          let comp1 =
                            let uu___6 =
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp in
                            if uu___6
                            then
                              let uu___7 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___8 =
                                     env.FStar_SMTEncoding_Env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___8.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___8.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___8.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___8.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___8.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___8.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___8.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___8.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___8.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___8.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___8.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___8.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___8.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___8.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___8.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___8.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___8.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___8.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___8.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___8.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___8.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___8.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___8.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___8.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___8.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___8.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                       =
                                       (uu___8.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___8.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                       =
                                       (uu___8.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___8.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___8.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___8.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___8.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___8.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___8.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___8.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___8.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___8.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___8.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___8.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___8.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___8.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___8.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___8.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___8.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___8.FStar_TypeChecker_Env.enable_defer_to_tac);
                                     FStar_TypeChecker_Env.unif_allow_ref_guards
                                       =
                                       (uu___8.FStar_TypeChecker_Env.unif_allow_ref_guards)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu___7
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu___6 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1 in
                            (args, uu___6)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu___4 with
                    | (formals, (pre_opt, res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___5 ->
                                  match uu___5 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu___6 = FStar_Util.prefix vars in
                                      (match uu___6 with
                                       | (uu___7, xxv) ->
                                           let xx =
                                             let uu___8 =
                                               let uu___9 =
                                                 let uu___10 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv in
                                                 (uu___10,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu___9 in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu___8 in
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         let uu___16 =
                                                           let uu___17 =
                                                             let uu___18 =
                                                               FStar_Ident.string_of_lid
                                                                 d in
                                                             FStar_SMTEncoding_Env.escape
                                                               uu___18 in
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             uu___17 xx in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu___16 in
                                                       (vapp, uu___15) in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu___14 in
                                                   ([[vapp]], vars, uu___13) in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu___11 uu___12 in
                                               let uu___11 =
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStar_Ident.string_of_lid
                                                       d in
                                                   FStar_SMTEncoding_Env.escape
                                                     uu___13 in
                                                 Prims.op_Hat
                                                   "disc_equation_" uu___12 in
                                               (uu___10,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 uu___11) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu___9 in
                                           [uu___8])
                                  | FStar_Syntax_Syntax.Projector (d, f) ->
                                      let uu___6 = FStar_Util.prefix vars in
                                      (match uu___6 with
                                       | (uu___7, xxv) ->
                                           let xx =
                                             let uu___8 =
                                               let uu___9 =
                                                 let uu___10 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv in
                                                 (uu___10,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu___9 in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu___8 in
                                           let f1 =
                                             {
                                               FStar_Syntax_Syntax.ppname = f;
                                               FStar_Syntax_Syntax.index =
                                                 Prims.int_zero;
                                               FStar_Syntax_Syntax.sort =
                                                 FStar_Syntax_Syntax.tun
                                             } in
                                           let tp_name =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d f1 in
                                           let prim_app =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tp_name, [xx]) in
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app) in
                                                   ([[vapp]], vars, uu___13) in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu___11 uu___12 in
                                               (uu___10,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name)) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu___9 in
                                           [uu___8])
                                  | uu___6 -> [])) in
                        let uu___5 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env in
                        (match uu___5 with
                         | (vars, guards, env', decls1, uu___6) ->
                             let uu___7 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None ->
                                   let uu___8 =
                                     FStar_SMTEncoding_Util.mk_and_l guards in
                                   (uu___8, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu___8 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env' in
                                   (match uu___8 with
                                    | (g, ds) ->
                                        let uu___9 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards) in
                                        (uu___9,
                                          (FStar_List.append decls1 ds))) in
                             (match uu___7 with
                              | (guard, decls11) ->
                                  let dummy_var =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ("@dummy",
                                        FStar_SMTEncoding_Term.dummy_sort) in
                                  let dummy_tm =
                                    FStar_SMTEncoding_Term.mkFreeV dummy_var
                                      FStar_Range.dummyRange in
                                  let should_thunk uu___8 =
                                    let is_type t =
                                      let uu___9 =
                                        let uu___10 =
                                          FStar_Syntax_Subst.compress t in
                                        uu___10.FStar_Syntax_Syntax.n in
                                      match uu___9 with
                                      | FStar_Syntax_Syntax.Tm_type uu___10
                                          -> true
                                      | uu___10 -> false in
                                    let is_squash t =
                                      let uu___9 =
                                        FStar_Syntax_Util.head_and_args t in
                                      match uu___9 with
                                      | (head, uu___10) ->
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_Syntax_Util.un_uinst head in
                                            uu___12.FStar_Syntax_Syntax.n in
                                          (match uu___11 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu___12;
                                                  FStar_Syntax_Syntax.index =
                                                    uu___13;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu___14;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu___15;_};_},
                                                uu___16)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu___12 -> false) in
                                    (((let uu___9 = FStar_Ident.nsstr lid in
                                       uu___9 <> "Prims") &&
                                        (let uu___9 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic) in
                                         Prims.op_Negation uu___9))
                                       &&
                                       (let uu___9 = is_squash t_norm in
                                        Prims.op_Negation uu___9))
                                      &&
                                      (let uu___9 = is_type t_norm in
                                       Prims.op_Negation uu___9) in
                                  let uu___8 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu___9 -> (false, vars) in
                                  (match uu___8 with
                                   | (thunked, vars1) ->
                                       let arity = FStar_List.length formals in
                                       let uu___9 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked in
                                       (match uu___9 with
                                        | (vname, vtok_opt, env1) ->
                                            let get_vtok uu___10 =
                                              FStar_Option.get vtok_opt in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [])
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu___10 ->
                                                  let uu___11 =
                                                    let uu___12 = get_vtok () in
                                                    (uu___12, []) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu___11 in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1 in
                                            let vapp =
                                              let uu___10 =
                                                let uu___11 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1 in
                                                (vname, uu___11) in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu___10 in
                                            let uu___10 =
                                              let vname_decl =
                                                let uu___11 =
                                                  let uu___12 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort) in
                                                  (vname, uu___12,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None) in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu___11 in
                                              let uu___11 =
                                                let env2 =
                                                  let uu___12 = env1 in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___12.FStar_SMTEncoding_Env.global_cache)
                                                  } in
                                                let uu___12 =
                                                  let uu___13 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt in
                                                  Prims.op_Negation uu___13 in
                                                if uu___12
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm in
                                              match uu___11 with
                                              | (tok_typing, decls2) ->
                                                  let uu___12 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname)) in
                                                        let uu___13 =
                                                          let uu___14 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                                          FStar_List.append
                                                            decls2 uu___14 in
                                                        let uu___14 =
                                                          let uu___15 =
                                                            let uu___16 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, []) in
                                                            FStar_All.pipe_left
                                                              (fun uu___17 ->
                                                                 FStar_Pervasives_Native.Some
                                                                   uu___17)
                                                              uu___16 in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu___15 in
                                                        (uu___13, uu___14)
                                                    | uu___13 when thunked ->
                                                        (decls2, env1)
                                                    | uu___13 ->
                                                        let vtok =
                                                          get_vtok () in
                                                        let vtok_decl =
                                                          FStar_SMTEncoding_Term.DeclFun
                                                            (vtok, [],
                                                              FStar_SMTEncoding_Term.Term_sort,
                                                              FStar_Pervasives_Native.None) in
                                                        let name_tok_corr_formula
                                                          pat =
                                                          let uu___14 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv in
                                                          let uu___15 =
                                                            let uu___16 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp) in
                                                            ([[pat]], vars1,
                                                              uu___16) in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu___14 uu___15 in
                                                        let name_tok_corr =
                                                          let uu___14 =
                                                            let uu___15 =
                                                              name_tok_corr_formula
                                                                vtok_app in
                                                            (uu___15,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu___14 in
                                                        let tok_typing1 =
                                                          let ff =
                                                            FStar_SMTEncoding_Term.mk_fv
                                                              ("ty",
                                                                FStar_SMTEncoding_Term.Term_sort) in
                                                          let f =
                                                            FStar_SMTEncoding_Util.mkFreeV
                                                              ff in
                                                          let vtok_app_r =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                              [uu___15] in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu___14 in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu___14 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu___15 =
                                                              let uu___16 =
                                                                let uu___17 =
                                                                  let uu___18
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing in
                                                                  let uu___19
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp in
                                                                  (uu___18,
                                                                    uu___19) in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu___17 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu___16) in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu___14 uu___15 in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname)) in
                                                        let uu___14 =
                                                          let uu___15 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                                          FStar_List.append
                                                            decls2 uu___15 in
                                                        (uu___14, env1) in
                                                  (match uu___12 with
                                                   | (tok_decl, env2) ->
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial in
                                                         FStar_List.append
                                                           uu___14 tok_decl in
                                                       (uu___13, env2)) in
                                            (match uu___10 with
                                             | (decls2, env2) ->
                                                 let uu___11 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t in
                                                   let uu___12 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env' in
                                                   match uu___12 with
                                                   | (encoded_res_t, decls)
                                                       ->
                                                       let uu___13 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t in
                                                       (encoded_res_t,
                                                         uu___13, decls) in
                                                 (match uu___11 with
                                                  | (encoded_res_t, ty_pred,
                                                     decls3) ->
                                                      let typingAx =
                                                        let uu___12 =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu___15 =
                                                              let uu___16 =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred) in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu___16) in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu___14 uu___15 in
                                                          (uu___13,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname)) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu___12 in
                                                      let freshness =
                                                        let uu___12 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New) in
                                                        if uu___12
                                                        then
                                                          let uu___13 =
                                                            let uu___14 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu___15 =
                                                              let uu___16 =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort) in
                                                              let uu___17 =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  () in
                                                              (vname,
                                                                uu___16,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu___17) in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu___14 uu___15 in
                                                          let uu___14 =
                                                            let uu___15 =
                                                              let uu___16 =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv in
                                                              pretype_axiom
                                                                uu___16 env2
                                                                vapp vars1 in
                                                            [uu___15] in
                                                          uu___13 :: uu___14
                                                        else [] in
                                                      let g =
                                                        let uu___12 =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                let uu___16 =
                                                                  let uu___17
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1 in
                                                                  typingAx ::
                                                                    uu___17 in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu___16 in
                                                              FStar_All.pipe_right
                                                                uu___15
                                                                FStar_SMTEncoding_Term.mk_decls_trivial in
                                                            FStar_List.append
                                                              decls3 uu___14 in
                                                          FStar_List.append
                                                            decls2 uu___13 in
                                                        FStar_List.append
                                                          decls11 uu___12 in
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
  fun env ->
    fun x ->
      fun t ->
        fun t_norm ->
          let uu___ =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu___ with
          | FStar_Pervasives_Native.None ->
              let uu___1 = encode_free_var false env x t t_norm [] in
              (match uu___1 with
               | (decls, env1) ->
                   let fvb =
                     FStar_SMTEncoding_Env.lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
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
  fun uninterpreted ->
    fun env ->
      fun lid ->
        fun t ->
          fun quals ->
            let tt = norm_before_encoding env t in
            let uu___ = encode_free_var uninterpreted env lid t tt quals in
            match uu___ with
            | (decls, env1) ->
                let uu___1 = FStar_Syntax_Util.is_smt_lemma t in
                if uu___1
                then
                  let uu___2 =
                    let uu___3 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu___3 in
                  (uu___2, env1)
                else (decls, env1)
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_elt Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      fun quals ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu___ ->
                fun lb ->
                  match uu___ with
                  | (decls, env1) ->
                      let uu___1 =
                        let uu___2 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu___2
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu___1 with
                       | (decls', env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.un_uinst hd in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu___2, c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             let uu___3 = FStar_Ident.string_of_lid effect_name in
             FStar_Util.starts_with "FStar.Tactics" uu___3
         | uu___2 -> false)
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Let_rec_unencodeable -> true | uu___ -> false
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en ->
    let uu___ = en in
    let uu___1 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth = (uu___.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv = (uu___.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels = (uu___.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu___1
    }
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun uu___ ->
      fun quals ->
        match uu___ with
        | (is_rec, bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu___1 = FStar_Util.first_N nbinders formals in
              match uu___1 with
              | (formals1, extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu___2 ->
                         fun uu___3 ->
                           match (uu___2, uu___3) with
                           | ({ FStar_Syntax_Syntax.binder_bv = formal;
                                FStar_Syntax_Syntax.binder_qual = uu___4;
                                FStar_Syntax_Syntax.binder_attrs = uu___5;_},
                              { FStar_Syntax_Syntax.binder_bv = binder;
                                FStar_Syntax_Syntax.binder_qual = uu___6;
                                FStar_Syntax_Syntax.binder_attrs = uu___7;_})
                               ->
                               let uu___8 =
                                 let uu___9 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu___9) in
                               FStar_Syntax_Syntax.NT uu___8) formals1
                      binders in
                  let extra_formals1 =
                    let uu___2 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun b ->
                              let uu___3 = b in
                              let uu___4 =
                                let uu___5 = b.FStar_Syntax_Syntax.binder_bv in
                                let uu___6 =
                                  FStar_Syntax_Subst.subst subst
                                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___5.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___5.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu___6
                                } in
                              {
                                FStar_Syntax_Syntax.binder_bv = uu___4;
                                FStar_Syntax_Syntax.binder_qual =
                                  (uu___3.FStar_Syntax_Syntax.binder_qual);
                                FStar_Syntax_Syntax.binder_attrs =
                                  (uu___3.FStar_Syntax_Syntax.binder_attrs)
                              })) in
                    FStar_All.pipe_right uu___2
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu___2 = FStar_Syntax_Subst.compress body in
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Util.args_of_binders extra_formals1 in
                      FStar_All.pipe_left FStar_Pervasives_Native.snd uu___4 in
                    FStar_Syntax_Syntax.extend_app_n uu___2 uu___3
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function t e =
              let tcenv =
                let uu___1 = env.FStar_SMTEncoding_Env.tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___1.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___1.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___1.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___1.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___1.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___1.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___1.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___1.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___1.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___1.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___1.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___1.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___1.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___1.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___1.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___1.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___1.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___1.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___1.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___1.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___1.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___1.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___1.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___1.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___1.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                    (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___1.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                    (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___1.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___1.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___1.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___1.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___1.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___1.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___1.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___1.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___1.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___1.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
                  FStar_TypeChecker_Env.enable_defer_to_tac =
                    (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
                  FStar_TypeChecker_Env.unif_allow_ref_guards =
                    (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
                } in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu___1 ->
                       fun uu___2 ->
                         match (uu___1, uu___2) with
                         | ({ FStar_Syntax_Syntax.binder_bv = x;
                              FStar_Syntax_Syntax.binder_qual = uu___3;
                              FStar_Syntax_Syntax.binder_attrs = uu___4;_},
                            { FStar_Syntax_Syntax.binder_bv = b;
                              FStar_Syntax_Syntax.binder_qual = uu___5;
                              FStar_Syntax_Syntax.binder_attrs = uu___6;_})
                             ->
                             let uu___7 =
                               let uu___8 = FStar_Syntax_Syntax.bv_to_name b in
                               (x, uu___8) in
                             FStar_Syntax_Syntax.NT uu___7) formals actuals in
                FStar_Syntax_Subst.subst_comp subst comp in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu___1 = FStar_Syntax_Subst.compress t1 in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu___1 in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals, comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu___1 ->
                    let uu___2 = FStar_Syntax_Util.unrefine t2 in
                    arrow_formals_comp_norm norm uu___2
                | uu___1 when Prims.op_Negation norm ->
                    let t_norm =
                      norm_with_steps
                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Exclude
                          FStar_TypeChecker_Env.Zeta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.EraseUniverses] tcenv t2 in
                    arrow_formals_comp_norm true t_norm
                | uu___1 ->
                    let uu___2 = FStar_Syntax_Syntax.mk_Total t2 in
                    ([], uu___2) in
              let aux t1 e1 =
                let uu___1 = FStar_Syntax_Util.abs_formals e1 in
                match uu___1 with
                | (binders, body, lopt) ->
                    let uu___2 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu___3 -> arrow_formals_comp_norm false t1 in
                    (match uu___2 with
                     | (formals, comp) ->
                         let nformals = FStar_List.length formals in
                         let nbinders = FStar_List.length binders in
                         let uu___3 =
                           if nformals < nbinders
                           then
                             let uu___4 = FStar_Util.first_N nformals binders in
                             match uu___4 with
                             | (bs0, rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt in
                                 let uu___5 = subst_comp formals bs0 comp in
                                 (bs0, body1, uu___5)
                           else
                             if nformals > nbinders
                             then
                               (let uu___5 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp) in
                                match uu___5 with
                                | (binders1, body1) ->
                                    let uu___6 =
                                      subst_comp formals binders1 comp in
                                    (binders1, body1, uu___6))
                             else
                               (let uu___6 = subst_comp formals binders comp in
                                (binders, body, uu___6)) in
                         (match uu___3 with
                          | (binders1, body1, comp1) ->
                              (binders1, body1, comp1))) in
              let uu___1 = aux t e in
              match uu___1 with
              | (binders, body, comp) ->
                  let uu___2 =
                    let uu___3 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp in
                    if uu___3
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body in
                      let uu___4 = aux comp1 body1 in
                      match uu___4 with
                      | (more_binders, body2, comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp) in
                  (match uu___2 with
                   | (binders1, body1, comp1) ->
                       let uu___3 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Pervasives.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None) in
                       (binders1, uu___3, comp1)) in
            (try
               (fun uu___1 ->
                  match () with
                  | () ->
                      let uu___2 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
                      if uu___2
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu___4 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu___5 ->
                                   fun lb ->
                                     match uu___5 with
                                     | (toks, typs, decls, env1) ->
                                         ((let uu___7 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           if uu___7
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           let uu___7 =
                                             let uu___8 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             declare_top_level_let env1
                                               uu___8
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm in
                                           match uu___7 with
                                           | (tok, decl, env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env)) in
                         match uu___4 with
                         | (toks, typs, decls, env1) ->
                             let toks_fvbs = FStar_List.rev toks in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten in
                             let env_decls = copy_env env1 in
                             let typs1 = FStar_List.rev typs in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu___5;
                                    FStar_Syntax_Syntax.lbeff = uu___6;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu___7;
                                    FStar_Syntax_Syntax.lbpos = uu___8;_}::[],
                                  t_norm::[], fvb::[]) ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid in
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm] in
                                     match uu___10 with
                                     | (tcenv', uu___11, e_t) ->
                                         let uu___12 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu___13 -> failwith "Impossible" in
                                         (match uu___12 with
                                          | (e1, t_norm1) ->
                                              ((let uu___13 = env2 in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___13.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1)) in
                                   (match uu___9 with
                                    | (env', e1, t_norm1) ->
                                        let uu___10 =
                                          destruct_bound_function t_norm1 e1 in
                                        (match uu___10 with
                                         | (binders, body, t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp in
                                             ((let uu___12 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu___12
                                               then
                                                 let uu___13 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu___14 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu___13 uu___14
                                               else ());
                                              (let uu___12 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu___12 with
                                               | (vars, _guards, env'1,
                                                  binder_decls, uu___13) ->
                                                   let uu___14 =
                                                     if
                                                       fvb.FStar_SMTEncoding_Env.fvb_thunked
                                                         && (vars = [])
                                                     then
                                                       let dummy_var =
                                                         FStar_SMTEncoding_Term.mk_fv
                                                           ("@dummy",
                                                             FStar_SMTEncoding_Term.dummy_sort) in
                                                       let dummy_tm =
                                                         FStar_SMTEncoding_Term.mkFreeV
                                                           dummy_var
                                                           FStar_Range.dummyRange in
                                                       let app =
                                                         let uu___15 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu___15 in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu___16 =
                                                          let uu___17 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn in
                                                          let uu___18 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu___17 fvb
                                                            uu___18 in
                                                        (vars, uu___16)) in
                                                   (match uu___14 with
                                                    | (vars1, app) ->
                                                        let uu___15 =
                                                          let is_logical =
                                                            let uu___16 =
                                                              let uu___17 =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body in
                                                              uu___17.FStar_Syntax_Syntax.n in
                                                            match uu___16
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu___17 ->
                                                                false in
                                                          let is_prims =
                                                            let uu___16 =
                                                              let uu___17 =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right in
                                                              FStar_All.pipe_right
                                                                uu___17
                                                                FStar_Syntax_Syntax.lid_of_fv in
                                                            FStar_All.pipe_right
                                                              uu___16
                                                              (fun lid ->
                                                                 let uu___17
                                                                   =
                                                                   let uu___18
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu___18 in
                                                                 FStar_Ident.lid_equals
                                                                   uu___17
                                                                   FStar_Parser_Const.prims_lid) in
                                                          let uu___16 =
                                                            (Prims.op_Negation
                                                               is_prims)
                                                              &&
                                                              ((FStar_All.pipe_right
                                                                  quals
                                                                  (FStar_List.contains
                                                                    FStar_Syntax_Syntax.Logic))
                                                                 ||
                                                                 is_logical) in
                                                          if uu___16
                                                          then
                                                            let uu___17 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app in
                                                            let uu___18 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1 in
                                                            (app, uu___17,
                                                              uu___18)
                                                          else
                                                            (let uu___18 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1 in
                                                             (app, app,
                                                               uu___18)) in
                                                        (match uu___15 with
                                                         | (pat, app1,
                                                            (body1, decls2))
                                                             ->
                                                             let eqn =
                                                               let uu___16 =
                                                                 let uu___17
                                                                   =
                                                                   let uu___18
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1) in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu___20) in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu___18
                                                                    uu___19 in
                                                                 let uu___18
                                                                   =
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu___20 in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu___19 in
                                                                 (uu___17,
                                                                   uu___18,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id)) in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu___16 in
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1 in
                                                                    eqn ::
                                                                    uu___21 in
                                                                    FStar_All.pipe_right
                                                                    uu___20
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu___19 in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu___18 in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu___17 in
                                                             (uu___16, env2)))))))
                               | uu___5 -> failwith "Impossible" in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu___5 =
                                   let uu___6 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel" in
                                   (uu___6, FStar_SMTEncoding_Term.Fuel_sort) in
                                 FStar_SMTEncoding_Term.mk_fv uu___5 in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel in
                               let env0 = env2 in
                               let uu___5 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu___6 ->
                                         fun fvb ->
                                           match uu___6 with
                                           | (gtoks, env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid in
                                               let g =
                                                 let uu___7 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu___7 in
                                               let gtok =
                                                 let uu___7 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu___7 in
                                               let env4 =
                                                 let uu___7 =
                                                   let uu___8 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm]) in
                                                   FStar_All.pipe_left
                                                     (fun uu___9 ->
                                                        FStar_Pervasives_Native.Some
                                                          uu___9) uu___8 in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu___7 in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2)) in
                               match uu___5 with
                               | (gtoks, env3) ->
                                   let gtoks1 = FStar_List.rev gtoks in
                                   let encode_one_binding env01 uu___6 t_norm
                                     uu___7 =
                                     match (uu___6, uu___7) with
                                     | ((fvb, g, gtok),
                                        { FStar_Syntax_Syntax.lbname = lbn;
                                          FStar_Syntax_Syntax.lbunivs = uvs;
                                          FStar_Syntax_Syntax.lbtyp = uu___8;
                                          FStar_Syntax_Syntax.lbeff = uu___9;
                                          FStar_Syntax_Syntax.lbdef = e;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu___10;
                                          FStar_Syntax_Syntax.lbpos = uu___11;_})
                                         ->
                                         let uu___12 =
                                           let uu___13 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm] in
                                           match uu___13 with
                                           | (tcenv', uu___14, e_t) ->
                                               let uu___15 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu___16 ->
                                                     failwith "Impossible" in
                                               (match uu___15 with
                                                | (e1, t_norm1) ->
                                                    ((let uu___16 = env3 in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___16.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1)) in
                                         (match uu___12 with
                                          | (env', e1, t_norm1) ->
                                              ((let uu___14 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding") in
                                                if uu___14
                                                then
                                                  let uu___15 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn in
                                                  let uu___16 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1 in
                                                  let uu___17 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1 in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu___15 uu___16 uu___17
                                                else ());
                                               (let uu___14 =
                                                  destruct_bound_function
                                                    t_norm1 e1 in
                                                match uu___14 with
                                                | (binders, body, tres_comp)
                                                    ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders) in
                                                    let uu___15 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp in
                                                    (match uu___15 with
                                                     | (pre_opt, tres) ->
                                                         ((let uu___17 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify") in
                                                           if uu___17
                                                           then
                                                             let uu___18 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn in
                                                             let uu___19 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders in
                                                             let uu___20 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body in
                                                             let uu___21 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu___18
                                                               uu___19
                                                               uu___20
                                                               uu___21
                                                           else ());
                                                          (let uu___17 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env' in
                                                           match uu___17 with
                                                           | (vars, guards,
                                                              env'1,
                                                              binder_decls,
                                                              uu___18) ->
                                                               let uu___19 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards in
                                                                    (uu___20,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    (guard,
                                                                    decls0)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard]) in
                                                                    (uu___21,
                                                                    decls0)) in
                                                               (match uu___19
                                                                with
                                                                | (guard,
                                                                   guard_decls)
                                                                    ->
                                                                    let binder_decls1
                                                                    =
                                                                    FStar_List.append
                                                                    binder_decls
                                                                    guard_decls in
                                                                    let decl_g
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___24 in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu___23 in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu___22 in
                                                                    (g,
                                                                    uu___21,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name")) in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu___20 in
                                                                    let env02
                                                                    =
                                                                    FStar_SMTEncoding_Env.push_zfuel_name
                                                                    env01
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                    g in
                                                                    let decl_g_tok
                                                                    =
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications")) in
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let rng =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let app =
                                                                    let uu___20
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu___20 in
                                                                    let mk_g_app
                                                                    args =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    rng
                                                                    (FStar_Pervasives.Inl
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    g))
                                                                    (fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    Prims.int_one)
                                                                    args in
                                                                    let gsapp
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm]) in
                                                                    uu___21
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu___20 in
                                                                    let gmax
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    []) in
                                                                    uu___21
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu___20 in
                                                                    let uu___20
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    (body_tm,
                                                                    decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                    (guard,
                                                                    uu___27) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___26 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu___25) in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu___23
                                                                    uu___24 in
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu___25 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    uu___23,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                    let eqn_f
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu___25) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero in
                                                                    uu___29
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu___28 in
                                                                    (gsapp,
                                                                    uu___27) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu___26 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu___25) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                    let uu___21
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm) in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu___23 in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu___22
                                                                    (fuel ::
                                                                    vars) in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu___22 in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1 in
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu___22 in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu___28) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___26
                                                                    uu___27 in
                                                                    (uu___25,
                                                                    tot_fun_axioms) in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu___24 in
                                                                    (uu___23,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___22 in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp in
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    (g_typing,
                                                                    d3) ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing) in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu___30) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___26 in
                                                                    [uu___25] in
                                                                    (d3,
                                                                    uu___24) in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])) in
                                                                    (match uu___21
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    g_typing)
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu___25 in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu___24 in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu___23 in
                                                                    let uu___23
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    (uu___22,
                                                                    uu___23,
                                                                    env02)))))))))) in
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1 in
                                     FStar_List.fold_left
                                       (fun uu___8 ->
                                          fun uu___9 ->
                                            match (uu___8, uu___9) with
                                            | ((decls2, eqns, env01),
                                               (gtok, ty, lb)) ->
                                                let uu___10 =
                                                  encode_one_binding env01
                                                    gtok ty lb in
                                                (match uu___10 with
                                                 | (decls', eqns', env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu___7 in
                                   (match uu___6 with
                                    | (decls2, eqns, env01) ->
                                        let uu___7 =
                                          let isDeclFun uu___8 =
                                            match uu___8 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu___9 -> true
                                            | uu___9 -> false in
                                          let uu___8 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten in
                                          FStar_All.pipe_right uu___8
                                            (fun decls3 ->
                                               let uu___9 =
                                                 FStar_List.fold_left
                                                   (fun uu___10 ->
                                                      fun elt ->
                                                        match uu___10 with
                                                        | (prefix_decls,
                                                           elts, rest) ->
                                                            let uu___11 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls) in
                                                            if uu___11
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu___13 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls in
                                                               match uu___13
                                                               with
                                                               | (elt_decl_funs,
                                                                  elt_rest)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                    elts,
                                                                    (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___14
                                                                    = elt in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___14.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___14.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___14.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3 in
                                               match uu___9 with
                                               | (prefix_decls, elts, rest)
                                                   ->
                                                   let uu___10 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial in
                                                   (uu___10, elts, rest)) in
                                        (match uu___7 with
                                         | (prefix_decls, elts, rest) ->
                                             let eqns1 = FStar_List.rev eqns in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01))) in
                             let uu___5 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___6 ->
                                        match uu___6 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                            -> true
                                        | uu___7 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t ->
                                          let uu___6 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t) in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu___6))) in
                             if uu___5
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___7 ->
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
                                | FStar_SMTEncoding_Env.Inner_let_rec names
                                    ->
                                    let plural =
                                      (FStar_List.length names) >
                                        Prims.int_one in
                                    let r =
                                      let uu___8 = FStar_List.hd names in
                                      FStar_All.pipe_right uu___8
                                        FStar_Pervasives_Native.snd in
                                    ((let uu___9 =
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names in
                                              FStar_All.pipe_right uu___13
                                                (FStar_String.concat ",") in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu___12
                                              (if plural
                                               then "their"
                                               else "its") in
                                          let uu___12 =
                                            FStar_Errors.get_ctx () in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu___11, r, uu___12) in
                                        [uu___10] in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu___9);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable ->
                 let msg =
                   let uu___2 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu___2 (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg) in
                 let uu___2 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial in
                 (uu___2, env))
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let nm =
        let uu___ = FStar_Syntax_Util.lid_of_sigelt se in
        match uu___ with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l in
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Syntax_Print.sigelt_to_string_short se in
          FStar_Util.format1 "While encoding top-level declaration `%s`"
            uu___2 in
        FStar_Errors.with_ctx uu___1 (fun uu___2 -> encode_sigelt' env se) in
      match uu___ with
      | (g, env1) ->
          let g1 =
            match g with
            | [] ->
                ((let uu___2 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env1.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "SMTEncoding") in
                  if uu___2
                  then FStar_Util.print1 "Skipped encoding of %s\n" nm
                  else ());
                 (let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Util.format1 "<Skipped %s/>" nm in
                      FStar_SMTEncoding_Term.Caption uu___4 in
                    [uu___3] in
                  FStar_All.pipe_right uu___2
                    FStar_SMTEncoding_Term.mk_decls_trivial))
            | uu___1 ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu___5 in
                    [uu___4] in
                  FStar_All.pipe_right uu___3
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Util.format1 "</end encoding %s>" nm in
                        FStar_SMTEncoding_Term.Caption uu___7 in
                      [uu___6] in
                    FStar_All.pipe_right uu___5
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append g uu___4 in
                FStar_List.append uu___2 uu___3 in
          (g1, env1)
and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      (let uu___1 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu___2
       else ());
      (let is_opaque_to_smt t =
         let uu___1 =
           let uu___2 = FStar_Syntax_Subst.compress t in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu___2)) -> s = "opaque_to_smt"
         | uu___2 -> false in
       let is_uninterpreted_by_smt t =
         let uu___1 =
           let uu___2 = FStar_Syntax_Subst.compress t in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu___2)) -> s = "uninterpreted_by_smt"
         | uu___2 -> false in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu___1 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu___1 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu___1 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu___1 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu___1 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___1 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___1 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu___1 =
             let uu___2 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname in
             Prims.op_Negation uu___2 in
           if uu___1
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu___3 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         ((ed.FStar_Syntax_Syntax.binders), tm,
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))))
                      tm.FStar_Syntax_Syntax.pos in
              let encode_action env1 a =
                let action_defn =
                  let uu___3 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn in
                  norm_before_encoding env1 uu___3 in
                let uu___3 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ in
                match uu___3 with
                | (formals, uu___4) ->
                    let arity = FStar_List.length formals in
                    let uu___5 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity in
                    (match uu___5 with
                     | (aname, atok, env2) ->
                         let uu___6 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2 in
                         (match uu___6 with
                          | (tm, decls) ->
                              let a_decls =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu___10 ->
                                              FStar_SMTEncoding_Term.Term_sort)) in
                                    (aname, uu___9,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action")) in
                                  FStar_SMTEncoding_Term.DeclFun uu___8 in
                                [uu___7;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))] in
                              let uu___7 =
                                let aux uu___8 uu___9 =
                                  match (uu___8, uu___9) with
                                  | ({ FStar_Syntax_Syntax.binder_bv = bv;
                                       FStar_Syntax_Syntax.binder_qual =
                                         uu___10;
                                       FStar_Syntax_Syntax.binder_attrs =
                                         uu___11;_},
                                     (env3, acc_sorts, acc)) ->
                                      let uu___12 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv in
                                      (match uu___12 with
                                       | (xxsym, xx, env4) ->
                                           let uu___13 =
                                             let uu___14 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                             uu___14 :: acc_sorts in
                                           (env4, uu___13, (xx :: acc))) in
                                FStar_List.fold_right aux formals
                                  (env2, [], []) in
                              (match uu___7 with
                               | (uu___8, xs_sorts, xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                   let a_eq =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               let uu___15 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts in
                                               (app, uu___15) in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu___14 in
                                           ([[app]], xs_sorts, uu___13) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu___11 uu___12 in
                                       (uu___10,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality")) in
                                     FStar_SMTEncoding_Util.mkAssume uu___9 in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu___9 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort) in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu___9 in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts in
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu___12 =
                                           let uu___13 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app) in
                                           ([[tok_app]], xs_sorts, uu___13) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu___11 uu___12 in
                                       (uu___10,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence")) in
                                     FStar_SMTEncoding_Util.mkAssume uu___9 in
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial in
                                     FStar_List.append decls uu___10 in
                                   (env2, uu___9)))) in
              let uu___3 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions in
              match uu___3 with
              | (env1, decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___1, uu___2) when
           FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu___3 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4)) in
           (match uu___3 with | (tname, ttok, env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___1, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let will_encode_definition =
             let uu___2 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | FStar_Syntax_Syntax.Projector uu___4 -> true
                       | FStar_Syntax_Syntax.Discriminator uu___4 -> true
                       | FStar_Syntax_Syntax.Irreducible -> true
                       | uu___4 -> false)) in
             Prims.op_Negation uu___2 in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              let uu___3 =
                let uu___4 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt) in
                encode_top_level_val uu___4 env fv t quals in
              match uu___3 with
              | (decls, env1) ->
                  let tname = FStar_Ident.string_of_lid lid in
                  let tsym =
                    let uu___4 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid in
                    FStar_Option.get uu___4 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym in
                      FStar_All.pipe_right uu___6
                        FStar_SMTEncoding_Term.mk_decls_trivial in
                    FStar_List.append decls uu___5 in
                  (uu___4, env1))
       | FStar_Syntax_Syntax.Sig_assume (l, us, f) ->
           let uu___1 = FStar_Syntax_Subst.open_univ_vars us f in
           (match uu___1 with
            | (uvs, f1) ->
                let env1 =
                  let uu___2 = env in
                  let uu___3 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___2.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___2.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___2.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu___3;
                    FStar_SMTEncoding_Env.warn =
                      (uu___2.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___2.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___2.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___2.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___2.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___2.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___2.FStar_SMTEncoding_Env.global_cache)
                  } in
                let f2 = norm_before_encoding env1 f1 in
                let uu___2 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1 in
                (match uu___2 with
                 | (f3, decls) ->
                     let g =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Print.lid_to_string l in
                                 FStar_Util.format1 "Assumption: %s" uu___8 in
                               FStar_Pervasives_Native.Some uu___7 in
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 = FStar_Ident.string_of_lid l in
                                 Prims.op_Hat "assumption_" uu___9 in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu___8 in
                             (f3, uu___6, uu___7) in
                           FStar_SMTEncoding_Util.mkAssume uu___5 in
                         [uu___4] in
                       FStar_All.pipe_right uu___3
                         FStar_SMTEncoding_Term.mk_decls_trivial in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs, uu___1) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu___2 =
             FStar_Util.fold_map
               (fun env1 ->
                  fun lb ->
                    let lid =
                      let uu___3 =
                        let uu___4 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        uu___4.FStar_Syntax_Syntax.fv_name in
                      uu___3.FStar_Syntax_Syntax.v in
                    let uu___3 =
                      let uu___4 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid in
                      FStar_All.pipe_left FStar_Option.isNone uu___4 in
                    if uu___3
                    then
                      let val_decl =
                        let uu___4 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___4.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___4.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___4.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___4.FStar_Syntax_Syntax.sigopts)
                        } in
                      let uu___4 = encode_sigelt' env1 val_decl in
                      match uu___4 with | (decls, env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
           (match uu___2 with
            | (env1, decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu___1,
             { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr b2t;
               FStar_Syntax_Syntax.lbunivs = uu___2;
               FStar_Syntax_Syntax.lbtyp = uu___3;
               FStar_Syntax_Syntax.lbeff = uu___4;
               FStar_Syntax_Syntax.lbdef = uu___5;
               FStar_Syntax_Syntax.lbattrs = uu___6;
               FStar_Syntax_Syntax.lbpos = uu___7;_}::[]),
            uu___8)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu___9 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one in
           (match uu___9 with
            | (tname, ttok, env1) ->
                let xx =
                  FStar_SMTEncoding_Term.mk_fv
                    ("x", FStar_SMTEncoding_Term.Term_sort) in
                let x = FStar_SMTEncoding_Util.mkFreeV xx in
                let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                let valid_b2t_x =
                  FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
                let decls =
                  let uu___10 =
                    let uu___11 =
                      let uu___12 =
                        let uu___13 =
                          let uu___14 = FStar_Syntax_Syntax.range_of_fv b2t in
                          let uu___15 =
                            let uu___16 =
                              let uu___17 =
                                let uu___18 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x]) in
                                (valid_b2t_x, uu___18) in
                              FStar_SMTEncoding_Util.mkEq uu___17 in
                            ([[b2t_x]], [xx], uu___16) in
                          FStar_SMTEncoding_Term.mkForall uu___14 uu___15 in
                        (uu___13, (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def") in
                      FStar_SMTEncoding_Util.mkAssume uu___12 in
                    [uu___11] in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu___10 in
                let uu___10 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                (uu___10, env1))
       | FStar_Syntax_Syntax.Sig_let (uu___1, uu___2) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___3 ->
                   match uu___3 with
                   | FStar_Syntax_Syntax.Discriminator uu___4 -> true
                   | uu___4 -> false))
           ->
           ((let uu___4 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu___4
             then
               let uu___5 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding discriminator '%s'\n" uu___5
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let (uu___1, lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStar_Ident.ns_of_lid l in
                        FStar_List.hd uu___4 in
                      FStar_Ident.string_of_id uu___3 in
                    uu___2 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___2 ->
                      match uu___2 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                          -> true
                      | uu___3 -> false)))
           ->
           ((let uu___3 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu___3
             then
               let uu___4 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding unfold let from Prims '%s'\n"
                 uu___4
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu___1) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___2 ->
                   match uu___2 with
                   | FStar_Syntax_Syntax.Projector uu___3 -> true
                   | uu___3 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
           let uu___2 = FStar_SMTEncoding_Env.try_lookup_free_var env l in
           (match uu___2 with
            | FStar_Pervasives_Native.Some uu___3 -> ([], env)
            | FStar_Pervasives_Native.None ->
                let se1 =
                  let uu___3 = se in
                  let uu___4 = FStar_Ident.range_of_lid l in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu___4;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3.FStar_Syntax_Syntax.sigopts)
                  } in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu___1) ->
           let bindings1 =
             FStar_List.map
               (fun lb ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp in
                  let uu___2 = lb in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___2.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___2.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___2.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___2.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___2.FStar_Syntax_Syntax.lbpos)
                  }) bindings in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses, uu___1) ->
           let uu___2 = encode_sigelts env ses in
           (match uu___2 with
            | (g, env1) ->
                let uu___3 =
                  FStar_List.fold_left
                    (fun uu___4 ->
                       fun elt ->
                         match uu___4 with
                         | (g', inversions) ->
                             let uu___5 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___6 ->
                                       match uu___6 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu___7;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu___8;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu___9;_}
                                           -> false
                                       | uu___7 -> true)) in
                             (match uu___5 with
                              | (elt_g', elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___6 = elt in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___6.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___6.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___6.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g in
                (match uu___3 with
                 | (g', inversions) ->
                     let uu___4 =
                       FStar_List.fold_left
                         (fun uu___5 ->
                            fun elt ->
                              match uu___5 with
                              | (decls, elts, rest) ->
                                  let uu___6 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___7 ->
                                            match uu___7 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu___8 -> true
                                            | uu___8 -> false)
                                         elt.FStar_SMTEncoding_Term.decls) in
                                  if uu___6
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu___8 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9 ->
                                               match uu___9 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu___10 -> true
                                               | uu___10 -> false)) in
                                     match uu___8 with
                                     | (elt_decls, elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___9 = elt in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___9.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___9.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___9.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g' in
                     (match uu___4 with
                      | (decls, elts, rest) ->
                          let uu___5 =
                            let uu___6 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial in
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append rest uu___9 in
                              FStar_List.append elts uu___8 in
                            FStar_List.append uu___6 uu___7 in
                          (uu___5, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t, universe_names, tps, k, uu___1, datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv in
           let is_injective =
             let uu___2 = FStar_Syntax_Subst.univ_var_opening universe_names in
             match uu___2 with
             | (usubst, uvs) ->
                 let uu___3 =
                   let uu___4 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs in
                   let uu___5 = FStar_Syntax_Subst.subst_binders usubst tps in
                   let uu___6 =
                     let uu___7 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst in
                     FStar_Syntax_Subst.subst uu___7 k in
                   (uu___4, uu___5, uu___6) in
                 (match uu___3 with
                  | (env1, tps1, k1) ->
                      let uu___4 = FStar_Syntax_Subst.open_term tps1 k1 in
                      (match uu___4 with
                       | (tps2, k2) ->
                           let uu___5 = FStar_Syntax_Util.arrow_formals k2 in
                           (match uu___5 with
                            | (uu___6, k3) ->
                                let uu___7 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2 in
                                (match uu___7 with
                                 | (tps3, env_tps, uu___8, us) ->
                                     let u_k =
                                       let uu___9 =
                                         let uu___10 =
                                           FStar_Syntax_Syntax.fvar t
                                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                                Prims.int_zero)
                                             FStar_Pervasives_Native.None in
                                         let uu___11 =
                                           let uu___12 =
                                             FStar_Syntax_Util.args_of_binders
                                               tps3 in
                                           FStar_Pervasives_Native.snd
                                             uu___12 in
                                         let uu___12 =
                                           FStar_Ident.range_of_lid t in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu___10 uu___11 uu___12 in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu___9 k3 in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero, uu___9)
                                           -> true
                                       | (FStar_Syntax_Syntax.U_succ u0,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name u0,
                                          FStar_Syntax_Syntax.U_name v0) ->
                                           FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name uu___9,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max us1,
                                          uu___9) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1 -> universe_leq u1 v))
                                       | (uu___9, FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown,
                                          uu___9) ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu___11 in
                                           failwith uu___10
                                       | (uu___9,
                                          FStar_Syntax_Syntax.U_unknown) ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu___11 in
                                           failwith uu___10
                                       | (FStar_Syntax_Syntax.U_unif uu___9,
                                          uu___10) ->
                                           let uu___11 =
                                             let uu___12 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu___12 in
                                           failwith uu___11
                                       | (uu___9, FStar_Syntax_Syntax.U_unif
                                          uu___10) ->
                                           let uu___11 =
                                             let uu___12 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu___12 in
                                           failwith uu___11
                                       | uu___9 -> false in
                                     let u_leq_u_k u =
                                       let uu___9 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u in
                                       universe_leq uu___9 u_k in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (tp.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                       let uu___9 = u_leq_u_k u_tp in
                                       if uu___9
                                       then true
                                       else
                                         (let uu___11 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp in
                                          match uu___11 with
                                          | (formals, uu___12) ->
                                              let uu___13 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals in
                                              (match uu___13 with
                                               | (uu___14, uu___15, uu___16,
                                                  u_formals) ->
                                                   FStar_Util.for_all
                                                     (fun u_formal ->
                                                        u_leq_u_k u_formal)
                                                     u_formals)) in
                                     FStar_List.forall2 tp_ok tps3 us)))) in
           ((let uu___3 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu___3
             then
               let uu___4 = FStar_Ident.string_of_lid t in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu___4
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Syntax_Syntax.Logic -> true
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu___4 -> false)) in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu___3 = c in
                 match uu___3 with
                 | (name, args, uu___4, uu___5, uu___6) ->
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu___10 ->
                                   match uu___10 with
                                   | (uu___11, sort, uu___12) -> sort)) in
                         (name, uu___9, FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None) in
                       FStar_SMTEncoding_Term.DeclFun uu___8 in
                     [uu___7]
               else
                 (let uu___4 = FStar_Ident.range_of_lid t in
                  FStar_SMTEncoding_Term.constructor_to_decl uu___4 c) in
             let inversion_axioms tapp vars =
               let uu___3 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l ->
                         let uu___4 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l in
                         FStar_All.pipe_right uu___4 FStar_Option.isNone)) in
               if uu___3
               then []
               else
                 (let uu___5 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort in
                  match uu___5 with
                  | (xxsym, xx) ->
                      let uu___6 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu___7 ->
                                fun l ->
                                  match uu___7 with
                                  | (out, decls) ->
                                      let uu___8 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l in
                                      (match uu___8 with
                                       | (uu___9, data_t) ->
                                           let uu___10 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t in
                                           (match uu___10 with
                                            | (args, res) ->
                                                let indices =
                                                  let uu___11 =
                                                    let uu___12 =
                                                      FStar_Syntax_Subst.compress
                                                        res in
                                                    uu___12.FStar_Syntax_Syntax.n in
                                                  match uu___11 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu___12, indices1) ->
                                                      indices1
                                                  | uu___12 -> [] in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env2 ->
                                                          fun uu___11 ->
                                                            match uu___11
                                                            with
                                                            | {
                                                                FStar_Syntax_Syntax.binder_bv
                                                                  = x;
                                                                FStar_Syntax_Syntax.binder_qual
                                                                  = uu___12;
                                                                FStar_Syntax_Syntax.binder_attrs
                                                                  = uu___13;_}
                                                                ->
                                                                let uu___14 =
                                                                  let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x in
                                                                    (uu___16,
                                                                    [xx]) in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu___15 in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env2 x
                                                                  uu___14)
                                                       env) in
                                                let uu___11 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1 in
                                                (match uu___11 with
                                                 | (indices1, decls') ->
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
                                                             (fun v ->
                                                                fun a ->
                                                                  let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    (uu___14,
                                                                    a) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu___13)
                                                             vars indices1
                                                         else [] in
                                                       let uu___13 =
                                                         let uu___14 =
                                                           let uu___15 =
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx in
                                                               let uu___18 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l in
                                                               (uu___17,
                                                                 uu___18) in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu___16 in
                                                           (out, uu___15) in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu___14 in
                                                       (uu___13,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, [])) in
                      (match uu___6 with
                       | (data_ax, decls) ->
                           let uu___7 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort in
                           (match uu___7 with
                            | (ffsym, ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu___8 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff]) in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu___8 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp in
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Ident.range_of_lid t in
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort) in
                                          let uu___14 =
                                            let uu___15 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort) in
                                            uu___15 :: vars in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu___13 uu___14 in
                                        let uu___13 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax) in
                                        ([[xx_has_type_sfuel]], uu___12,
                                          uu___13) in
                                      FStar_SMTEncoding_Term.mkForall uu___10
                                        uu___11 in
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStar_Ident.string_of_lid t in
                                        Prims.op_Hat
                                          "fuel_guarded_inversion_" uu___12 in
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        uu___11 in
                                    (uu___9,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu___10) in
                                  FStar_SMTEncoding_Util.mkAssume uu___8 in
                                let uu___8 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append decls uu___8))) in
             let uu___3 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu___4 ->
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Syntax.mk_Total k in
                         (tps, uu___7) in
                       FStar_Syntax_Syntax.Tm_arrow uu___6 in
                     FStar_Syntax_Syntax.mk uu___5 k.FStar_Syntax_Syntax.pos in
               let k2 = norm_before_encoding env k1 in
               FStar_Syntax_Util.arrow_formals k2 in
             match uu___3 with
             | (formals, res) ->
                 let uu___4 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env in
                 (match uu___4 with
                  | (vars, guards, env', binder_decls, uu___5) ->
                      let arity = FStar_List.length vars in
                      let uu___6 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity in
                      (match uu___6 with
                       | (tname, ttok, env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, []) in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards in
                           let tapp =
                             let uu___7 =
                               let uu___8 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               (tname, uu___8) in
                             FStar_SMTEncoding_Util.mkApp uu___7 in
                           let uu___7 =
                             let tname_decl =
                               let uu___8 =
                                 let uu___9 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv in
                                             Prims.op_Hat tname uu___11 in
                                           let uu___11 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv in
                                           (uu___10, uu___11, false))) in
                                 let uu___10 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     () in
                                 (tname, uu___9,
                                   FStar_SMTEncoding_Term.Term_sort, uu___10,
                                   false) in
                               constructor_or_logic_type_decl uu___8 in
                             let uu___8 =
                               match vars with
                               | [] ->
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, []) in
                                       FStar_All.pipe_left
                                         (fun uu___12 ->
                                            FStar_Pervasives_Native.Some
                                              uu___12) uu___11 in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu___10 in
                                   ([], uu___9)
                               | uu___9 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token")) in
                                   let ttok_fresh =
                                     let uu___10 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         () in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu___10 in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars in
                                   let pats = [[ttok_app]; [tapp]] in
                                   let name_tok_corr =
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           FStar_Ident.range_of_lid t in
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp) in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu___14) in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu___12 uu___13 in
                                       (uu___11,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok)) in
                                     FStar_SMTEncoding_Util.mkAssume uu___10 in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1) in
                             match uu___8 with
                             | (tok_decls, env2) ->
                                 ((FStar_List.append tname_decl tok_decls),
                                   env2) in
                           (match uu___7 with
                            | (decls, env2) ->
                                let kindingAx =
                                  let uu___8 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp in
                                  match uu___8 with
                                  | (k1, decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu___12 in
                                              (uu___11,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok)) in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu___10 in
                                          [uu___9]
                                        else [] in
                                      let rng = FStar_Ident.range_of_lid t in
                                      let tot_fun_axioms =
                                        let uu___9 =
                                          FStar_List.map
                                            (fun uu___10 ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu___9 true in
                                      let uu___9 =
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                let uu___14 =
                                                  let uu___15 =
                                                    let uu___16 =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1) in
                                                        ([[tapp]], vars,
                                                          uu___18) in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu___17 in
                                                    (tot_fun_axioms, uu___16) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu___15 in
                                                (uu___14,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok)) in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu___13 in
                                            [uu___12] in
                                          FStar_List.append karr uu___11 in
                                        FStar_All.pipe_right uu___10
                                          FStar_SMTEncoding_Term.mk_decls_trivial in
                                      FStar_List.append decls1 uu___9 in
                                let aux =
                                  let uu___8 =
                                    let uu___9 = inversion_axioms tapp vars in
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            FStar_Ident.range_of_lid t in
                                          pretype_axiom uu___13 env2 tapp
                                            vars in
                                        [uu___12] in
                                      FStar_All.pipe_right uu___11
                                        FStar_SMTEncoding_Term.mk_decls_trivial in
                                    FStar_List.append uu___9 uu___10 in
                                  FStar_List.append kindingAx uu___8 in
                                let g =
                                  let uu___8 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial in
                                  FStar_List.append uu___8
                                    (FStar_List.append binder_decls aux) in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d, uu___1, t, uu___2, n_tps, mutuals) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let t1 = norm_before_encoding env t in
           let uu___3 = FStar_Syntax_Util.arrow_formals t1 in
           (match uu___3 with
            | (formals, t_res) ->
                let arity = FStar_List.length formals in
                let uu___4 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity in
                (match uu___4 with
                 | (ddconstrsym, ddtok, env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
                     let uu___5 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort in
                     (match uu___5 with
                      | (fuel_var, fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                          let uu___6 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1 in
                          (match uu___6 with
                           | (vars, guards, env', binder_decls, names) ->
                               let fields =
                                 FStar_All.pipe_right names
                                   (FStar_List.mapi
                                      (fun n ->
                                         fun x ->
                                           let projectible = true in
                                           let uu___7 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x in
                                           (uu___7,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible))) in
                               let datacons =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       () in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu___8, true) in
                                 let uu___8 =
                                   let uu___9 = FStar_Ident.range_of_lid d in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu___9 in
                                 FStar_All.pipe_right uu___7 uu___8 in
                               let app =
                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                   ddtok_tm vars in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards in
                               let xvars =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               let dapp =
                                 FStar_SMTEncoding_Util.mkApp
                                   (ddconstrsym, xvars) in
                               let uu___7 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm in
                               (match uu___7 with
                                | (tok_typing, decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu___8::uu___9 ->
                                          let ff =
                                            FStar_SMTEncoding_Term.mk_fv
                                              ("ty",
                                                FStar_SMTEncoding_Term.Term_sort) in
                                          let f =
                                            FStar_SMTEncoding_Util.mkFreeV ff in
                                          let vtok_app_l =
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              ddtok_tm [ff] in
                                          let vtok_app_r =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              [uu___11] in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu___10 in
                                          let uu___10 =
                                            FStar_Ident.range_of_lid d in
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu___12) in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu___10 uu___11
                                      | uu___8 -> tok_typing in
                                    let uu___8 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1 in
                                    (match uu___8 with
                                     | (vars', guards', env'', decls_formals,
                                        uu___9) ->
                                         let uu___10 =
                                           let xvars1 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars' in
                                           let dapp1 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (ddconstrsym, xvars1) in
                                           FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                             (FStar_Pervasives_Native.Some
                                                fuel_tm) t_res env'' dapp1 in
                                         (match uu___10 with
                                          | (ty_pred', decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards' in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu___11 ->
                                                    let uu___12 =
                                                      let uu___13 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          () in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu___13 in
                                                    [uu___12] in
                                              let encode_elim uu___11 =
                                                let uu___12 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res in
                                                match uu___12 with
                                                | (head, args) ->
                                                    let uu___13 =
                                                      let uu___14 =
                                                        FStar_Syntax_Subst.compress
                                                          head in
                                                      uu___14.FStar_Syntax_Syntax.n in
                                                    (match uu___13 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu___14;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu___15;_},
                                                          uu___16)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name in
                                                         let uu___17 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu___17 with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv2 ->
                                                                    fv2
                                                                  | uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu___21 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu___20) in
                                                                    FStar_Errors.raise_error
                                                                    uu___19
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu___19 in
                                                                    if
                                                                    uu___18
                                                                    then
                                                                    let uu___19
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu___19]
                                                                    else [])) in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1 in
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    fun
                                                                    uu___21
                                                                    ->
                                                                    match 
                                                                    (uu___20,
                                                                    uu___21)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu___23 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    (uu___23,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu___24
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu___24
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu___25
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu___25
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu___19 in
                                                              (match uu___18
                                                               with
                                                               | (uu___19,
                                                                  arg_vars,
                                                                  elim_eqns_or_guards,
                                                                  uu___20) ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___26
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu___28) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___27 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___25,
                                                                    uu___26) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                   let lex_t
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu___23,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu___22 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu___21 in
                                                                   let subterm_ordering
                                                                    =
                                                                    let prec
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu___24
                                                                    dapp1 in
                                                                    [uu___23]))) in
                                                                    FStar_All.pipe_right
                                                                    uu___21
                                                                    FStar_List.flatten in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___26
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu___28) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___27 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___25,
                                                                    uu___26) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                   let uu___21
                                                                    =
                                                                    let tot_or_gtot_inductive_codomain
                                                                    c =
                                                                    let is_inductive
                                                                    l =
                                                                    let uu___22
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    env1.FStar_SMTEncoding_Env.tcenv
                                                                    l in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    FStar_Syntax_Syntax.sigel
                                                                    =
                                                                    FStar_Syntax_Syntax.Sig_inductive_typ
                                                                    uu___23;
                                                                    FStar_Syntax_Syntax.sigrng
                                                                    = uu___24;
                                                                    FStar_Syntax_Syntax.sigquals
                                                                    = uu___25;
                                                                    FStar_Syntax_Syntax.sigmeta
                                                                    = uu___26;
                                                                    FStar_Syntax_Syntax.sigattrs
                                                                    = uu___27;
                                                                    FStar_Syntax_Syntax.sigopts
                                                                    = uu___28;_}
                                                                    -> true
                                                                    | 
                                                                    uu___23
                                                                    -> false in
                                                                    let res =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.is_tot_or_gtot_comp
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___23 in
                                                                    if
                                                                    uu___22
                                                                    then
                                                                    false
                                                                    else
                                                                    (let uu___24
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c) in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___25)
                                                                    ->
                                                                    FStar_Util.for_some
                                                                    (fun
                                                                    mutual ->
                                                                    (is_inductive
                                                                    mutual)
                                                                    &&
                                                                    (FStar_Syntax_Util.is_fvar
                                                                    mutual
                                                                    head1))
                                                                    mutuals) in
                                                                    res in
                                                                    let uu___22
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    fun
                                                                    formal ->
                                                                    fun var
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    (formal.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (bs, c)
                                                                    ->
                                                                    (match bs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    uu___25
                                                                    when
                                                                    let uu___26
                                                                    =
                                                                    tot_or_gtot_inductive_codomain
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___26
                                                                    ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    bs env'' in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (bs',
                                                                    guards'1,
                                                                    _env',
                                                                    bs_decls,
                                                                    uu___27)
                                                                    ->
                                                                    let fun_app
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    var in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu___28
                                                                    bs' in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    [uu___34] in
                                                                    [uu___33] in
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards'1 in
                                                                    let uu___36
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    (uu___35,
                                                                    uu___36) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___34 in
                                                                    (uu___32,
                                                                    bs',
                                                                    uu___33) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___30
                                                                    uu___31 in
                                                                    uu___29
                                                                    ::
                                                                    codomain_prec_l in
                                                                    (uu___28,
                                                                    (FStar_List.append
                                                                    bs_decls
                                                                    cod_decls))))))
                                                                    ([], [])
                                                                    formals
                                                                    vars in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    (match codomain_prec_l
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    ([],
                                                                    cod_decls)
                                                                    | 
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___31
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    codomain_prec_l in
                                                                    (ty_pred,
                                                                    uu___33) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___32 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___30,
                                                                    uu___31) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "well-founded ordering on codomain"),
                                                                    (Prims.op_Hat
                                                                    "well_founded_ordering_on_comdain_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___26 in
                                                                    [uu___25] in
                                                                    (uu___24,
                                                                    cod_decls)) in
                                                                   (match uu___21
                                                                    with
                                                                    | 
                                                                    (codomain_ordering,
                                                                    codomain_decls)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    arg_decls
                                                                    codomain_decls),
                                                                    (FStar_List.append
                                                                    [typing_inversion;
                                                                    subterm_ordering]
                                                                    codomain_ordering)))))
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name in
                                                         let uu___14 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu___14 with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv2 ->
                                                                    fv2
                                                                  | uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu___18 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu___17) in
                                                                    FStar_Errors.raise_error
                                                                    uu___16
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu___16 in
                                                                    if
                                                                    uu___15
                                                                    then
                                                                    let uu___16
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu___16]
                                                                    else [])) in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1 in
                                                              let uu___15 =
                                                                let uu___16 =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu___17
                                                                    ->
                                                                    fun
                                                                    uu___18
                                                                    ->
                                                                    match 
                                                                    (uu___17,
                                                                    uu___18)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu___20 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    (uu___20,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu___21
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu___21
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu___22
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu___22
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu___16 in
                                                              (match uu___15
                                                               with
                                                               | (uu___16,
                                                                  arg_vars,
                                                                  elim_eqns_or_guards,
                                                                  uu___17) ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___23
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu___25) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___24 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___22,
                                                                    uu___23) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___20
                                                                    uu___21 in
                                                                    (uu___19,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___18 in
                                                                   let lex_t
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu___20,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu___19 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu___18 in
                                                                   let subterm_ordering
                                                                    =
                                                                    let prec
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu___21
                                                                    dapp1 in
                                                                    [uu___20]))) in
                                                                    FStar_All.pipe_right
                                                                    uu___18
                                                                    FStar_List.flatten in
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___23
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu___25) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___24 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___22,
                                                                    uu___23) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___20
                                                                    uu___21 in
                                                                    (uu___19,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___18 in
                                                                   let uu___18
                                                                    =
                                                                    let tot_or_gtot_inductive_codomain
                                                                    c =
                                                                    let is_inductive
                                                                    l =
                                                                    let uu___19
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    env1.FStar_SMTEncoding_Env.tcenv
                                                                    l in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    FStar_Syntax_Syntax.sigel
                                                                    =
                                                                    FStar_Syntax_Syntax.Sig_inductive_typ
                                                                    uu___20;
                                                                    FStar_Syntax_Syntax.sigrng
                                                                    = uu___21;
                                                                    FStar_Syntax_Syntax.sigquals
                                                                    = uu___22;
                                                                    FStar_Syntax_Syntax.sigmeta
                                                                    = uu___23;
                                                                    FStar_Syntax_Syntax.sigattrs
                                                                    = uu___24;
                                                                    FStar_Syntax_Syntax.sigopts
                                                                    = uu___25;_}
                                                                    -> true
                                                                    | 
                                                                    uu___20
                                                                    -> false in
                                                                    let res =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Util.is_tot_or_gtot_comp
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___20 in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    false
                                                                    else
                                                                    (let uu___21
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c) in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___22)
                                                                    ->
                                                                    FStar_Util.for_some
                                                                    (fun
                                                                    mutual ->
                                                                    (is_inductive
                                                                    mutual)
                                                                    &&
                                                                    (FStar_Syntax_Util.is_fvar
                                                                    mutual
                                                                    head1))
                                                                    mutuals) in
                                                                    res in
                                                                    let uu___19
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    fun
                                                                    formal ->
                                                                    fun var
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    (formal.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    (match uu___21
                                                                    with
                                                                    | 
                                                                    (bs, c)
                                                                    ->
                                                                    (match bs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    uu___22
                                                                    when
                                                                    let uu___23
                                                                    =
                                                                    tot_or_gtot_inductive_codomain
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___23
                                                                    ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    bs env'' in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (bs',
                                                                    guards'1,
                                                                    _env',
                                                                    bs_decls,
                                                                    uu___24)
                                                                    ->
                                                                    let fun_app
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    var in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu___25
                                                                    bs' in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    [uu___31] in
                                                                    [uu___30] in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards'1 in
                                                                    let uu___33
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    (uu___32,
                                                                    uu___33) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___31 in
                                                                    (uu___29,
                                                                    bs',
                                                                    uu___30) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___27
                                                                    uu___28 in
                                                                    uu___26
                                                                    ::
                                                                    codomain_prec_l in
                                                                    (uu___25,
                                                                    (FStar_List.append
                                                                    bs_decls
                                                                    cod_decls))))))
                                                                    ([], [])
                                                                    formals
                                                                    vars in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    (match codomain_prec_l
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    ([],
                                                                    cod_decls)
                                                                    | 
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___28
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    codomain_prec_l in
                                                                    (ty_pred,
                                                                    uu___30) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu___29 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___27,
                                                                    uu___28) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___25
                                                                    uu___26 in
                                                                    (uu___24,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "well-founded ordering on codomain"),
                                                                    (Prims.op_Hat
                                                                    "well_founded_ordering_on_comdain_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___23 in
                                                                    [uu___22] in
                                                                    (uu___21,
                                                                    cod_decls)) in
                                                                   (match uu___18
                                                                    with
                                                                    | 
                                                                    (codomain_ordering,
                                                                    codomain_decls)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    arg_decls
                                                                    codomain_decls),
                                                                    (FStar_List.append
                                                                    [typing_inversion;
                                                                    subterm_ordering]
                                                                    codomain_ordering)))))
                                                     | uu___14 ->
                                                         ((let uu___16 =
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d in
                                                               let uu___19 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu___18
                                                                 uu___19 in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu___17) in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu___16);
                                                          ([], []))) in
                                              let uu___11 = encode_elim () in
                                              (match uu___11 with
                                               | (decls2, elim) ->
                                                   let g =
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           let uu___15 =
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu___22 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___21 in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu___20) in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu___19 in
                                                                 [uu___18] in
                                                               FStar_List.append
                                                                 uu___17
                                                                 proxy_fresh in
                                                             FStar_All.pipe_right
                                                               uu___16
                                                               FStar_SMTEncoding_Term.mk_decls_trivial in
                                                           let uu___16 =
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 let uu___19
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok)) in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu___28) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___26
                                                                    uu___27 in
                                                                    (uu___25,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___24 in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu___31
                                                                    vars' in
                                                                    let uu___31
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu___30,
                                                                    uu___31) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu___26 in
                                                                    [uu___25] in
                                                                    uu___23
                                                                    ::
                                                                    uu___24 in
                                                                    uu___21
                                                                    ::
                                                                    uu___22 in
                                                                   FStar_List.append
                                                                    uu___20
                                                                    elim in
                                                                 FStar_All.pipe_right
                                                                   uu___19
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu___18 in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu___17 in
                                                           FStar_List.append
                                                             uu___15 uu___16 in
                                                         FStar_List.append
                                                           decls3 uu___14 in
                                                       FStar_List.append
                                                         decls2 uu___13 in
                                                     FStar_List.append
                                                       binder_decls uu___12 in
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial in
                                                     FStar_List.append
                                                       uu___13 g in
                                                   (uu___12, env1))))))))))
and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun ses ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu___ ->
              fun se ->
                match uu___ with
                | (g, env1) ->
                    let uu___1 = encode_sigelt env1 se in
                    (match uu___1 with
                     | (g', env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      let encode_binding b uu___ =
        match uu___ with
        | (i, decls, env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu___1 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort in
                 ((let uu___2 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu___2
                   then
                     let uu___3 = FStar_Syntax_Print.bv_to_string x in
                     let uu___4 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n" uu___3
                       uu___4 uu___5
                   else ());
                  (let uu___2 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1 in
                   match uu___2 with
                   | (t, decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 = FStar_Util.digest_of_string t_hash in
                             Prims.op_Hat uu___6
                               (Prims.op_Hat "_" (Prims.string_of_int i)) in
                           Prims.op_Hat "x_" uu___5 in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu___4 in
                       (match uu___3 with
                        | (xxsym, xx, env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu___4 = FStar_Options.log_queries () in
                              if uu___4
                              then
                                let uu___5 =
                                  let uu___6 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu___8 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)" uu___6
                                    uu___7 uu___8 in
                                FStar_Pervasives_Native.Some uu___5
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              let uu___4 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial in
                              let uu___5 =
                                let uu___6 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append decls' uu___6 in
                              FStar_List.append uu___4 uu___5 in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x, (uu___1, t)) ->
                 let t_norm = norm_before_encoding env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None in
                 let uu___2 = encode_free_var false env1 fv t t_norm [] in
                 (match uu___2 with
                  | (g, env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env'))) in
      let uu___ =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env) in
      match uu___ with | (uu___1, decls, env1) -> (decls, env1)
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu___ ->
              match uu___ with
              | (l, uu___1, uu___2) ->
                  let uu___3 =
                    let uu___4 = FStar_SMTEncoding_Term.fv_name l in
                    (uu___4, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None) in
                  FStar_SMTEncoding_Term.DeclFun uu___3)) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu___ ->
              match uu___ with
              | (l, uu___1, uu___2) ->
                  let uu___3 =
                    let uu___4 = FStar_SMTEncoding_Term.fv_name l in
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_SMTEncoding_Term.Echo uu___5)
                      uu___4 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu___6 in
                    [uu___5] in
                  uu___3 :: uu___4)) in
    (prefix, suffix)
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Util.psmap_empty () in
        let uu___3 = let uu___4 = FStar_Util.psmap_empty () in (uu___4, []) in
        let uu___4 =
          let uu___5 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu___5 FStar_Ident.string_of_lid in
        let uu___5 = FStar_Util.smap_create (Prims.of_int (100)) in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu___2;
          FStar_SMTEncoding_Env.fvar_bindings = uu___3;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu___4;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu___5
        } in
      [uu___1] in
    FStar_ST.op_Colon_Equals last_env uu___
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn ->
    fun tcenv ->
      let uu___ = FStar_ST.op_Bang last_env in
      match uu___ with
      | [] -> failwith "No env; call init first!"
      | e::uu___1 ->
          let uu___2 = e in
          let uu___3 = FStar_Ident.string_of_lid cmn in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___2.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___2.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___2.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn = (uu___2.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___2.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___2.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___2.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu___3;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___2.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___2.FStar_SMTEncoding_Env.global_cache)
          }
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env ->
    let uu___ = FStar_ST.op_Bang last_env in
    match uu___ with
    | [] -> failwith "Empty env stack"
    | uu___1::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
let (push_env : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang last_env in
    match uu___1 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
let (pop_env : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang last_env in
    match uu___1 with
    | [] -> failwith "Popping an empty stack"
    | uu___2::tl -> FStar_ST.op_Colon_Equals last_env tl
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu___ -> FStar_Common.snapshot push_env last_env ()
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_env last_env depth
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let (snapshot :
  Prims.string -> (FStar_TypeChecker_Env.solver_depth_t * unit)) =
  fun msg ->
    FStar_Util.atomically
      (fun uu___ ->
         let uu___1 = snapshot_env () in
         match uu___1 with
         | (env_depth, ()) ->
             let uu___2 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot () in
             (match uu___2 with
              | (varops_depth, ()) ->
                  let uu___3 = FStar_SMTEncoding_Z3.snapshot msg in
                  (match uu___3 with
                   | (z3_depth, ()) ->
                       ((env_depth, varops_depth, z3_depth), ()))))
let (rollback :
  Prims.string ->
    FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg ->
    fun depth ->
      FStar_Util.atomically
        (fun uu___ ->
           let uu___1 =
             match depth with
             | FStar_Pervasives_Native.Some (s1, s2, s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None) in
           match uu___1 with
           | (env_depth, varops_depth, z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
let (push : Prims.string -> unit) = fun msg -> let uu___ = snapshot msg in ()
let (pop : Prims.string -> unit) =
  fun msg -> rollback msg FStar_Pervasives_Native.None
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env -> []
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun fact_db_ids ->
      fun d ->
        match (fact_db_ids, d) with
        | (uu___::uu___1, FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___2 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___2.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___2.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___2.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu___ -> d
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env ->
    fun fact_db_ids ->
      fun elt ->
        let uu___ = elt in
        let uu___1 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids)) in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key = (uu___.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu___1;
          FStar_SMTEncoding_Term.a_names =
            (uu___.FStar_SMTEncoding_Term.a_names)
        }
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env ->
    fun lid ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Ident.ns_of_lid lid in
            FStar_Ident.lid_of_ids uu___3 in
          FStar_SMTEncoding_Term.Namespace uu___2 in
        let uu___2 = open_fact_db_tags env in uu___1 :: uu___2 in
      (FStar_SMTEncoding_Term.Name lid) :: uu___
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_elt Prims.list *
        FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu___ = encode_sigelt env se in
      match uu___ with
      | (g, env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let (recover_caching_and_update_env :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env ->
    fun decls ->
      FStar_All.pipe_right decls
        (FStar_List.collect
           (fun elt ->
              if
                elt.FStar_SMTEncoding_Term.key = FStar_Pervasives_Native.None
              then [elt]
              else
                (let uu___1 =
                   let uu___2 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu___2 in
                 match uu___1 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None ->
                     ((let uu___3 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu___3 elt);
                      [elt]))))
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv ->
    fun se ->
      let caption decls =
        let uu___ = FStar_Options.log_queries () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu___4 (FStar_String.concat ", ") in
              Prims.op_Hat "encoding sigelt " uu___3 in
            FStar_SMTEncoding_Term.Caption uu___2 in
          uu___1 :: decls
        else decls in
      (let uu___1 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu___2
       else ());
      (let env =
         let uu___1 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu___1 tcenv in
       let uu___1 = encode_top_level_facts env se in
       match uu___1 with
       | (decls, env1) ->
           (set_env env1;
            (let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1) in
                 FStar_All.pipe_right uu___5
                   FStar_SMTEncoding_Term.decls_list_of in
               caption uu___4 in
             FStar_SMTEncoding_Z3.giveZ3 uu___3)))
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env ->
    fun name ->
      fun decls ->
        let caption decls1 =
          let uu___ = FStar_Options.log_queries () in
          if uu___
          then
            let msg = Prims.op_Hat "Externals for " name in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)] in
        set_env
          (let uu___1 = env in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu___1 =
             let uu___2 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env) in
             FStar_All.pipe_right uu___2 FStar_SMTEncoding_Term.decls_list_of in
           caption uu___1 in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv ->
    fun modul ->
      let uu___ = (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
      if uu___
      then ([], [])
      else
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu___2 ->
             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh
               ();
             (let name =
                let uu___4 =
                  FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                FStar_Util.format2 "%s %s"
                  (if modul.FStar_Syntax_Syntax.is_interface
                   then "interface"
                   else "module") uu___4 in
              (let uu___5 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
               if uu___5
               then
                 let uu___6 =
                   FStar_All.pipe_right
                     (FStar_List.length
                        modul.FStar_Syntax_Syntax.declarations)
                     Prims.string_of_int in
                 FStar_Util.print2
                   "+++++++++++Encoding externals for %s ... %s declarations\n"
                   name uu___6
               else ());
              (let env =
                 let uu___5 = get_env modul.FStar_Syntax_Syntax.name tcenv in
                 FStar_All.pipe_right uu___5
                   FStar_SMTEncoding_Env.reset_current_module_fvbs in
               let encode_signature env1 ses =
                 FStar_All.pipe_right ses
                   (FStar_List.fold_left
                      (fun uu___5 ->
                         fun se ->
                           match uu___5 with
                           | (g, env2) ->
                               let uu___6 = encode_top_level_facts env2 se in
                               (match uu___6 with
                                | (g', env3) ->
                                    ((FStar_List.append g g'), env3)))
                      ([], env1)) in
               let uu___5 =
                 encode_signature
                   (let uu___6 = env in
                    {
                      FStar_SMTEncoding_Env.bvar_bindings =
                        (uu___6.FStar_SMTEncoding_Env.bvar_bindings);
                      FStar_SMTEncoding_Env.fvar_bindings =
                        (uu___6.FStar_SMTEncoding_Env.fvar_bindings);
                      FStar_SMTEncoding_Env.depth =
                        (uu___6.FStar_SMTEncoding_Env.depth);
                      FStar_SMTEncoding_Env.tcenv =
                        (uu___6.FStar_SMTEncoding_Env.tcenv);
                      FStar_SMTEncoding_Env.warn = false;
                      FStar_SMTEncoding_Env.nolabels =
                        (uu___6.FStar_SMTEncoding_Env.nolabels);
                      FStar_SMTEncoding_Env.use_zfuel_name =
                        (uu___6.FStar_SMTEncoding_Env.use_zfuel_name);
                      FStar_SMTEncoding_Env.encode_non_total_function_typ =
                        (uu___6.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                      FStar_SMTEncoding_Env.current_module_name =
                        (uu___6.FStar_SMTEncoding_Env.current_module_name);
                      FStar_SMTEncoding_Env.encoding_quantifier =
                        (uu___6.FStar_SMTEncoding_Env.encoding_quantifier);
                      FStar_SMTEncoding_Env.global_cache =
                        (uu___6.FStar_SMTEncoding_Env.global_cache)
                    }) modul.FStar_Syntax_Syntax.declarations in
               match uu___5 with
               | (decls, env1) ->
                   (give_decls_to_z3_and_set_env env1 name decls;
                    (let uu___8 =
                       FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                     if uu___8
                     then
                       FStar_Util.print1 "Done encoding externals for %s\n"
                         name
                     else ());
                    (let uu___8 =
                       FStar_All.pipe_right env1
                         FStar_SMTEncoding_Env.get_current_module_fvbs in
                     (decls, uu___8))))))
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv ->
    fun tcmod ->
      fun uu___ ->
        match uu___ with
        | (decls, fvbs) ->
            let uu___1 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
            if uu___1
            then ()
            else
              (let name =
                 let uu___3 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu___3 in
               (let uu___4 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                if uu___4
                then
                  let uu___5 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu___5
                else ());
               (let env =
                  let uu___4 = get_env tcmod.FStar_Syntax_Syntax.name tcenv in
                  FStar_All.pipe_right uu___4
                    FStar_SMTEncoding_Env.reset_current_module_fvbs in
                let env1 =
                  let uu___4 = FStar_All.pipe_right fvbs FStar_List.rev in
                  FStar_All.pipe_right uu___4
                    (FStar_List.fold_left
                       (fun env2 ->
                          fun fvb ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env2) env) in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu___5 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                 if uu___5
                 then
                   FStar_Util.print1
                     "Done encoding externals from cache for %s\n" name
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
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        FStar_Errors.with_ctx "While encoding a query"
          (fun uu___ ->
             (let uu___2 =
                let uu___3 = FStar_TypeChecker_Env.current_module tcenv in
                FStar_Ident.string_of_lid uu___3 in
              FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
                uu___2);
             (let env =
                let uu___2 = FStar_TypeChecker_Env.current_module tcenv in
                get_env uu___2 tcenv in
              let uu___2 =
                let rec aux bindings =
                  match bindings with
                  | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                      let uu___3 = aux rest in
                      (match uu___3 with
                       | (out, rest1) ->
                           let t =
                             let uu___4 =
                               FStar_Syntax_Util.destruct_typ_as_formula
                                 x.FStar_Syntax_Syntax.sort in
                             match uu___4 with
                             | FStar_Pervasives_Native.Some uu___5 ->
                                 let uu___6 =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None
                                     FStar_Syntax_Syntax.t_unit in
                                 FStar_Syntax_Util.refine uu___6
                                   x.FStar_Syntax_Syntax.sort
                             | uu___5 -> x.FStar_Syntax_Syntax.sort in
                           let t1 =
                             norm_with_steps
                               [FStar_TypeChecker_Env.Eager_unfolding;
                               FStar_TypeChecker_Env.Beta;
                               FStar_TypeChecker_Env.Simplify;
                               FStar_TypeChecker_Env.Primops;
                               FStar_TypeChecker_Env.EraseUniverses]
                               env.FStar_SMTEncoding_Env.tcenv t in
                           let uu___4 =
                             let uu___5 =
                               FStar_Syntax_Syntax.mk_binder
                                 (let uu___6 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___6.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___6.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }) in
                             uu___5 :: out in
                           (uu___4, rest1))
                  | uu___3 -> ([], bindings) in
                let uu___3 = aux tcenv.FStar_TypeChecker_Env.gamma in
                match uu___3 with
                | (closing, bindings) ->
                    let uu___4 =
                      FStar_Syntax_Util.close_forall_no_univs
                        (FStar_List.rev closing) q in
                    (uu___4, bindings) in
              match uu___2 with
              | (q1, bindings) ->
                  let uu___3 = encode_env_bindings env bindings in
                  (match uu___3 with
                   | (env_decls, env1) ->
                       ((let uu___5 =
                           ((FStar_TypeChecker_Env.debug tcenv
                               FStar_Options.Medium)
                              ||
                              (FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug tcenv)
                                 (FStar_Options.Other "SMTEncoding")))
                             ||
                             (FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug tcenv)
                                (FStar_Options.Other "SMTQuery")) in
                         if uu___5
                         then
                           let uu___6 = FStar_Syntax_Print.term_to_string q1 in
                           FStar_Util.print1 "Encoding query formula {: %s\n"
                             uu___6
                         else ());
                        (let uu___5 =
                           FStar_Util.record_time
                             (fun uu___6 ->
                                FStar_SMTEncoding_EncodeTerm.encode_formula
                                  q1 env1) in
                         match uu___5 with
                         | ((phi, qdecls), ms) ->
                             let uu___6 =
                               let uu___7 =
                                 FStar_TypeChecker_Env.get_range tcenv in
                               FStar_SMTEncoding_ErrorReporting.label_goals
                                 use_env_msg uu___7 phi in
                             (match uu___6 with
                              | (labels, phi1) ->
                                  let uu___7 = encode_labels labels in
                                  (match uu___7 with
                                   | (label_prefix, label_suffix) ->
                                       let caption =
                                         let uu___8 =
                                           FStar_Options.log_queries () in
                                         if uu___8
                                         then
                                           let uu___9 =
                                             let uu___10 =
                                               let uu___11 =
                                                 FStar_Syntax_Print.term_to_string
                                                   q1 in
                                               Prims.op_Hat
                                                 "Encoding query formula : "
                                                 uu___11 in
                                             FStar_SMTEncoding_Term.Caption
                                               uu___10 in
                                           [uu___9]
                                         else [] in
                                       let query_prelude =
                                         let uu___8 =
                                           let uu___9 =
                                             let uu___10 =
                                               let uu___11 =
                                                 FStar_All.pipe_right
                                                   label_prefix
                                                   FStar_SMTEncoding_Term.mk_decls_trivial in
                                               let uu___12 =
                                                 let uu___13 =
                                                   FStar_All.pipe_right
                                                     caption
                                                     FStar_SMTEncoding_Term.mk_decls_trivial in
                                                 FStar_List.append qdecls
                                                   uu___13 in
                                               FStar_List.append uu___11
                                                 uu___12 in
                                             FStar_List.append env_decls
                                               uu___10 in
                                           FStar_All.pipe_right uu___9
                                             (recover_caching_and_update_env
                                                env1) in
                                         FStar_All.pipe_right uu___8
                                           FStar_SMTEncoding_Term.decls_list_of in
                                       let qry =
                                         let uu___8 =
                                           let uu___9 =
                                             FStar_SMTEncoding_Util.mkNot
                                               phi1 in
                                           let uu___10 =
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               "@query" in
                                           (uu___9,
                                             (FStar_Pervasives_Native.Some
                                                "query"), uu___10) in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu___8 in
                                       let suffix =
                                         FStar_List.append
                                           [FStar_SMTEncoding_Term.Echo
                                              "<labels>"]
                                           (FStar_List.append label_suffix
                                              [FStar_SMTEncoding_Term.Echo
                                                 "</labels>";
                                              FStar_SMTEncoding_Term.Echo
                                                "Done!"]) in
                                       ((let uu___9 =
                                           ((FStar_TypeChecker_Env.debug
                                               tcenv FStar_Options.Medium)
                                              ||
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    tcenv)
                                                 (FStar_Options.Other
                                                    "SMTEncoding")))
                                             ||
                                             (FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   tcenv)
                                                (FStar_Options.Other
                                                   "SMTQuery")) in
                                         if uu___9
                                         then
                                           FStar_Util.print_string
                                             "} Done encoding\n"
                                         else ());
                                        (let uu___10 =
                                           (((FStar_TypeChecker_Env.debug
                                                tcenv FStar_Options.Medium)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     tcenv)
                                                  (FStar_Options.Other
                                                     "SMTEncoding")))
                                              ||
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    tcenv)
                                                 (FStar_Options.Other
                                                    "SMTQuery")))
                                             ||
                                             (FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   tcenv)
                                                (FStar_Options.Other "Time")) in
                                         if uu___10
                                         then
                                           FStar_Util.print1
                                             "Encoding took %sms\n"
                                             (Prims.string_of_int ms)
                                         else ());
                                        (query_prelude, labels, qry, suffix)))))))))